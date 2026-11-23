module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Basic

variable (D : D7)

theorem orth_embedding_isometry (x y : (D.sp.X 0).V) :
    (D.sp.Y 0).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega) x y

theorem orth_embedding_injective : Function.Injective (D.sp.iXY 0) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (D.sp.X 0).nondeg.1 x fun y => ?_
  rw [← orth_embedding_isometry, hx]; simp

variable {D} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he hz in
theorem orth_embedding_mem_orth_plus (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xplus (lf D F0)) := by
  have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip (D.sp.iXY 0 x)) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      show (hS D).hT (F0.e a) (D.sp.iXY 0 x) = 0
      rw [he]
      exact c_symm0 (D.sp.hyp_orthX a x).1
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      show (hS D).hT F0.z (D.sp.iXY 0 x) = 0
      rw [hz]
      unfold D7.zmOf
      rw [map_smulₛₗ, LinearMap.smul_apply, c_symm0 (D.sp.zm_orth x), smul_zero]
  exact c_mem_orth.2 fun v hv => h hv

include he in
theorem eq_zero_of_embedding_mem_isotropic {x : (D.sp.X 0).V} (hx : D.sp.iXY 0 x ∈ Xsp (lf D F0)) : x = 0 := by
  have hx' : D.sp.iXY 0 x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by rw [← he]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx'
  have h0 : ∀ i, c i = 0 := by
    intro i
    have h1 := (D.sp.hyp_orthX i x).2

    rw [← hc, map_sum, LinearMap.sum_apply] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simpa using h1
  apply orth_embedding_injective D
  rw [← hc, map_zero]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]


include he hz in
theorem orth_space_posDef_every_place (hT : 0 < Tu D u) : Cnt.IsPosDef (D.sp.X 0).hT := by
  intro τ x hx
  have h1 := p_posX D (Tu D u) hT (lf D F0) τ (D.sp.iXY 0 x) (orth_embedding_mem_orth_plus F0 he hz x)
    (fun h => hx (eq_zero_of_embedding_mem_isotropic F0 he h))
  unfold nrm at h1
  rwa [orth_embedding_isometry] at h1

end Basic

section Lat

variable {D : D7} {T : D.host.E} (Λ : LatV D) (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem mem_orthLattice_iff_mem_sub {x : (D.sp.X 0).V} : x ∈ L0X D Λ F ↔ D.sp.iXY 0 x ∈ L0sub Λ F := Iff.rfl

theorem orthLattice_isIntegral_of_unimodular (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F) := by
  intro x hx y hy
  obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hx).1.1
  obtain ⟨l', hl', ξ', hξ', e'⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hy).1.1
  rw [← orth_embedding_isometry, ← e, ← e']
  have h1 : (hS D).hT l ξ' = 0 := c_symm0 (c_mem_orth.1 hl.2 ξ' hξ')
  have h2 : (hS D).hT ξ l' = 0 := c_mem_orth.1 hl'.2 ξ hξ
  have h3 : (hS D).hT ξ ξ' = 0 := p_X_iso F hξ hξ'
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [h1, h2, h3, add_zero, add_zero, add_zero]
  exact i_int Λ hu hl.1 hl'.1

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem decay_length_sufficient {m k r c B : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (ha : B * m ^ 5 ≤ k) :
    (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 ≤ (9 * c + 3) * k * m ^ 2 := by
  have hm2 : 2 ≤ m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hr1 : r + 1 = m / 2 := by linarith
  have e : (r + 1) * (12 * (c * r ^ 2) + B * m ^ 2 / 2 + B * m ^ 4 + 12 * (r + 1) ^ 2) + 1 =
      6 * m * (c * r ^ 2) + (B * m ^ 3) / 4 + (B * m ^ 5) / 2 + (m / 2) * (12 * (m / 2) ^ 2) + 1 := by rw [hr1]; ring
  have p1 : 6 * m * (c * r ^ 2) ≤ 2 * (c * k * m ^ 2) := by
    have a : r ^ 2 ≤ m ^ 2 / 4 := by nlinarith
    have b : c * r ^ 2 ≤ c * (m ^ 2 / 4) := mul_le_mul_of_nonneg_left a hc
    have d : 6 * m * (c * r ^ 2) ≤ 6 * m * (c * (m ^ 2 / 4)) := mul_le_mul_of_nonneg_left b (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hc (sq_nonneg m)) (by linarith : 0 ≤ k - m)]
  have m35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have p2 : B * m ^ 3 ≤ k := le_trans (mul_le_mul_of_nonneg_left m35 hB) ha
  have p4 : (m / 2) * (12 * (m / 2) ^ 2) ≤ (3 / 2) * (k * m ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : 0 ≤ k - m)]
  have p5 : (1 : ℝ) ≤ (1 / 2) * (k * m ^ 2) := by nlinarith
  have hm4 : 4 ≤ m ^ 2 := by nlinarith
  have p6 : k ≤ (1 / 4) * (k * m ^ 2) := by nlinarith [mul_nonneg hk0 (sub_nonneg.2 hm4)]
  have hU : 0 ≤ c * k * m ^ 2 := by positivity
  rw [e]
  have t : (9 * c + 3) * k * m ^ 2 = 9 * (c * k * m ^ 2) + 3 * (k * m ^ 2) := by ring
  rw [t]
  linarith

theorem le_max_four (a b c d : ℝ) : a ≤ max (max a b) (max c d) ∧ b ≤ max (max a b) (max c d) ∧
    c ≤ max (max a b) (max c d) ∧ d ≤ max (max a b) (max c d) :=
  ⟨le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {u u' : D.what₂.Word}

theorem height_pow_mono_constant (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h : |c'| + 2 ≤ c) (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := by
  have h1 : c' ≤ c := by linarith [le_abs_self c']
  have h2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have mono := rows_HHZ_mono large₂ hrd h1 h2 Z
  have o := rows_one_le_HHZ' D large₂ c' Z
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  calc HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) ≤ HHZ D large₂.sc.b c' Z ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) := Real.rpow_le_rpow (by linarith) mono (by positivity)

theorem switch_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz what₂ hrows Z hZ
  have h0 := h hH F0 he hz what₂ hrows Z hZ
  unfold MeanLe at h0 ⊢
  have hB : HHZ D large₂.sc.b c' Z ^ (c' * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ ≤
      HHZ D large₂.sc.b c Z ^ (c * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ := by
    refine mul_le_mul_of_nonneg_right (height_pow_mono_constant large₂ (d_rdE_pos hH.1) h1 Z) ?_
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold nV
    exact D.R.k_even.pow_nonneg _
  exact h0.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB))

theorem partner_count_bound_mono_constant {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : |c'| + 2 ≤ c)
    (h : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ
  refine (h hH F0 he hz Λ hΛ F' hF' hgen hR Z hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  have hrd := d_rdE_pos hH.1
  have k1 : c' ≤ c := by linarith [le_abs_self c']
  have k2 : 2 ≤ c + c' := by linarith [neg_abs_le c']
  have hc : 0 ≤ c := by linarith [abs_nonneg c']
  have ma := rows_HHZ_mono large₂ hrd k1 k2 (ZhatL (lf D F0) F')
  have mb := rows_HHZ_mono large₂ hrd k1 k2 Z
  have oa := rows_one_le_HHZ' D large₂ c' (ZhatL (lf D F0) F')
  have ob := rows_one_le_HHZ' D large₂ c' Z
  have o : 1 ≤ HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z := one_le_mul_of_one_le_of_one_le oa ob
  have hp : c' ^ D.R.f ≤ c ^ D.R.f :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  refine mul_le_mul hp ?_ (Real.rpow_nonneg (by linarith) _) (pow_nonneg hc _)
  calc (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c' * (D.R.rS : ℝ) ^ 2)
      ≤ (HHZ D large₂.sc.b c' (ZhatL (lf D F0) F') * HHZ D large₂.sc.b c' Z) ^ (c * (D.R.rS : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le o (by gcongr)
    _ ≤ _ := Real.rpow_le_rpow (by linarith) (mul_le_mul ma mb (by linarith) (by linarith)) (by positivity)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end
