module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle334
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.NormOne

variable {p : ℕ} [Fact p.Prime]

theorem norm_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ ≤ 1 := by
  rw [(X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_sigma_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
  rw [hy]
  exact norm_alg_le X E v _

theorem norm_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (u : (X.G.P.W v)ˣ) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ = 1 ∧
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ = 1 := by
  have h1 : ((u : X.G.P.W v) * ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := Units.mul_inv u
  have e1 : ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ *
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, norm_one]
  have e2 : ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ *
      ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, map_one, norm_one]
  have a1 := norm_alg_le X E v (u : X.G.P.W v)
  have a2 := norm_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have b1 := norm_sigma_alg_le X E v (u : X.G.P.W v)
  have b2 := norm_sigma_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have n1 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))
  have n2 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))
  have n3 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))))
  have n4 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))))
  constructor <;> nlinarith

theorem norm_sigma_alg (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ =
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (X.G.P.setting v).p_unif
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, (norm_unit X E v u).1, (norm_unit X E v u).2]

theorem norm_sigma (X : Sys p) (E : CEmb X.G) (v : X.Pl) (y : X.G.P.Qq v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v y))‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) y
  simp only [map_div₀, norm_div, norm_sigma_alg]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.Qq v) :
    ‖twG X E v s y‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  simp only [twG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  generalize s.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((X.G.P.σ v) ^ (n + 1)) y = X.G.P.σ v (((X.G.P.σ v) ^ n) y) := by rw [pow_succ']; rfl
    rw [e, norm_sigma, ih]

theorem prod_parity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if s.val % 2 = 1 then b else a) = (a * b) ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [Fin.prod_univ_eq_prod_range (fun i => if i % 2 = 1 then b else a) (m + m)]
  have : m + m = 2 * m := by ring
  rw [this, Nat.mul_div_cancel_left m (by norm_num)]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h0 : ¬ (2 * m) % 2 = 1 := by omega
    simp only [h1, h0, if_true, if_false]
    rw [mul_assoc]

theorem prod_parity_pos {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if IsOddPos s then b else a) = (a * b) ^ (n / 2) := by
  rw [← prod_parity a b n hn]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1
  · rw [if_pos h, if_pos (show IsOddPos s from h)]
  · rw [if_neg h, if_neg (show ¬ IsOddPos s from h)]

end GlobalTheory.TwU.NormOne

namespace GlobalTheory.TwU.NormOne

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have h : IsIntegral ℚ (TaylorLogMetric.embT D τ x) := (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom
  exact mem_algebraicClosure_iff.2 h.isAlgebraic

end GlobalTheory.TwU.NormOne


open GlobalTheory.TwU.NormOne in
theorem GlobalTheory.TwV.prod_embT_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  intro D _ hT _ _ _ _ _ _ u _ w hg _ _ H X _ std _ J S hPos ι hι z hz
  have hl : ∀ τ, ι (TaylorLogMetric.embT D τ z) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D τ z) := by
    intro τ
    rw [TaylorLogMetric.lamC, dite_eq_left (embT_mem_qbar D τ z)]
    exact hι ⟨_, embT_mem_qbar D τ z⟩
  rw [map_prod, norm_prod]
  simp only [hl]
  rw [← Fintype.prod_equiv (hT.gat_pos u w hg) (fun σ => ‖TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg σ) z)‖) _ (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  have hP : ∀ v s x, TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) =
      twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj x else x)) := hPos
  refine Finset.prod_eq_one fun v _ => ?_
  have hs : ∀ s : Fin ((sysS H X std).G.P.n' v),
      ‖twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj z else z))‖ =
        if IsOddPos s then ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v (D.host.conj z)))‖
        else ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v z))‖ := by
    intro s
    split_ifs <;> exact norm_twG _ _ _ _ _
  simp only [hP]
  refine (Finset.prod_congr rfl fun s _ => hs s).trans ?_
  rw [prod_parity_pos _ _ _ ((sysS H X std).G.P.setting v).even, ← norm_mul, ← map_mul, ← map_mul, ← map_mul, hz,
    map_one, map_one, map_one, norm_one, one_pow]
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.UnitPos

theorem norm_twG_le {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.W v) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y)‖ ≤ 1 := by
  have h := E.compat v s.val y
  have e : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y) =
      E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) y))) := rfl
  rw [e, h, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

theorem norm_twG_unit {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : (X.G.P.W v)ˣ) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_le X E v s (y : X.G.P.W v)
  have h2 := norm_twG_le X E v s ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have hm : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v)) *
      twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hn := congrArg norm hm
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ := norm_nonneg _
  have h0' : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))‖ := norm_nonneg _
  nlinarith

end GlobalTheory.TwV.UnitPos

namespace GlobalTheory.TwV.UnitPos

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom

end GlobalTheory.TwV.UnitPos


open GlobalTheory.TwV.UnitPos in
theorem GlobalTheory.TwV.UnitPos.norm_embT_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι b hb hloc τ
  obtain ⟨⟨v, s⟩, rfl⟩ := (hT.gat_pos u w hg).surjective τ
  have hq := embT_mem_qbar D ((hT.gat_pos u w hg) ⟨v, s⟩) b
  have e1 : ι (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) := by
    rw [TaylorLogMetric.lamC, dite_eq_left hq]
    exact hι ⟨_, hq⟩
  rw [e1, hS v s b]
  obtain ⟨y, hy⟩ := hloc v
  split_ifs with ho
  · have hc : J.rho std v (D.host.conj b) = algebraMap _ _ (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) := by
      have h1 : J.rho std v (D.host.conj b) * J.rho std v b = 1 := by
        rw [← map_mul, mul_comm, hb, map_one]
      have h2 : algebraMap ((sysS H X std).G.P.W v) ((sysS H X std).G.P.Qq v) (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) *
          J.rho std v b = 1 := by
        rw [hy, ← map_mul, Units.inv_mul, map_one]
      have hne : J.rho std v b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    rw [hc]
    exact norm_twG_unit _ S.E v s _
  · rw [hy]
    exact norm_twG_unit _ S.E v s y
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem reGL_finCongr_twice {R : Type} [CommRing R] {a b : ℕ} (h1 : a = b) (h2 : b = a) (x : GL (Fin a) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h2) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h1) x) = x := by
  subst h1
  apply Units.ext
  ext r s
  rfl



theorem ptS_isPt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj La hLa
  obtain ⟨⟨hr, hx⟩, -⟩ := hD (j + 1) hj La hLa
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  refine ⟨Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2, fun v => ?_, ?_⟩
  · obtain ⟨g, hg'⟩ := (Formalism.L2.G.Cmp.isLattice_iff _ (La.2 v)).1 (hLa v)
    exact Classical.epsilon_spec (p := fun g0 : GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v) =>
      La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g0 : Matrix _ _ _)) ⟨g, by rw [hg', Formalism.L2.G.Cmp.colSpan_eq]⟩
  · have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      show (dite (j + 1 ≤ D.R.m) _ _ : PtCh _ _).y = _
      rw [dite_eq_left hj]
    rw [hx, hy, reGL_finCongr_twice]
    exact (Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩).1

end GlobalTheory.TwV.DelA
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.ScaleUnit

theorem norm_ltC_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  obtain ⟨-, hAt, -⟩ := S.curve
  obtain ⟨h1, h2, h3, hLam, hOk⟩ := hAt
  have hU : GL3Theta.IsModelU S.g.lam (TaylorLogMetric.lamOf D t.cc t.δ) S.g.C := hLam ▸ hOk.1
  have hu := (GlobalTheory.UnitModel.modelEx_holds D _ S.g.lam t.cc t.δ h1 h2 h3).2.2 S.g.C hU
  unfold ltC
  rw [norm_inv, norm_mul, hu, norm_wToC_unit, mul_one, inv_one]

end GlobalTheory.TwU.ScaleUnit
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem latticeTupleLevelZero_point_isComponentPoint : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v), (∀ v, La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g v).1) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 g (J.pt std 0 (Nat.zero_le _) La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD La hLa
  obtain ⟨⟨hr, he⟩, -⟩ := hD 0 (Nat.zero_le _) La hLa
  simp only [Joint.cp, cpAt, chAt] at he
  refine ⟨basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2, fun v => ?_, ?_⟩
  · unfold basesAt
    obtain ⟨g0, hg0⟩ := Formalism.MainNotions.G.KAat.exists_bases1 La.2 hLa
    exact Classical.epsilon_spec (⟨g0 v, hg0 v⟩ : ∃ g : GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v),
      La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g : Matrix _ _ _))
  · rw [he]
    convert (Classical.epsilon_spec (GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
      (basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2))).1 using 1
    ext i j
    rfl

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem castSt_y_castCls {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) : (castSt h S).y (castCls h i c) = S.y c := by
  subst h; rfl

theorem exists_isDetOf_uPts (D : D7) (i : ℕ) (hi : i ≤ D.R.m)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 := by
  have hd := det_unitary_adelic_point_gram_step_norm_one D i hi x
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1)).toMonoidHom (Matrix.GeneralLinearGroup.det x.1), ?_⟩, ?_⟩
  · simp only [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, Formalism.L2.DIV.conjId] at hd
    have hd' := congrArg Units.val hd
    simp only [Units.val_mul, Units.coe_map, Units.val_one, MonoidHom.coe_coe] at hd'
    show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, Matrix.scalar_apply, inclE]
    rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]
    exact hd'
  · ext
    simp [Formalism.L2.Herm.IsDetOf, Matrix.GeneralLinearGroup.det]

theorem tw_at_rep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β c
  obtain ⟨y, hy⟩ := exists_isDetOf_uPts D (j + 1) hj (((I.at' j hj).st.K β).y c)
  rw [J.tw j hj β _ y hy]
  have hrep : (J.St (j + 1) hj).y (castCls (X.onCh j hj) (j + 1) c.1) = ((I.at' j hj).st.K β).y c := by
    have e := J.st j hj
    revert e
    generalize J.St (j + 1) hj = St'
    intro e
    subst e
    rw [castSt_y_castCls]
    exact (GlobalTheory.TwU.StepCharts.y_eq (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) c).symm
  rw [J.tie.dt (j + 1) hj _ y (by rw [hy, hrep])]

end GlobalTheory.TwV
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  first | exact @GlobalTheory.TwV.sNum_lev_site | exact GlobalTheory.TwV.sNum_lev_site | (intros; apply GlobalTheory.TwV.sNum_lev_site <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_tuple_adelic_point_step_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_succ_isPt | exact GlobalTheory.TwV.Joint.pt_succ_isPt | (intros; apply GlobalTheory.TwV.Joint.pt_succ_isPt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_tuple_adelic_point_step_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  first | exact @GlobalTheory.TwV.Joint.isPt_pt_zero | exact GlobalTheory.TwV.Joint.isPt_pt_zero | (intros; apply GlobalTheory.TwV.Joint.isPt_pt_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_tuple_bases_span_at_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  first | exact @GlobalTheory.TwV.Joint.basesAt_span | exact GlobalTheory.TwV.Joint.basesAt_span | (intros; apply GlobalTheory.TwV.Joint.basesAt_span <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  first | exact @GlobalTheory.TwV.chart_succ_eq | exact GlobalTheory.TwV.chart_succ_eq | (intros; apply GlobalTheory.TwV.chart_succ_eq <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.intOff_xi0_of_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  first | exact @GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | exact GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | (intros; apply GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes <;> assumption)
end
