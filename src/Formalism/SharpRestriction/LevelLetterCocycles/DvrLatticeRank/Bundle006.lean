module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfEMkAeval
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfSSplit
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem uniformiser_ring_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) : p9R D HW := by
  unfold adm1 Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeLocal at h1
  intro l _ hl K LL hG T hT
  have h9 := (h1 l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT
  unfold Formalism.MainNotions.DeltaInvariantLattices.p9 at h9
  have hpe : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : ((HW l).W K 1 LL hG).s = 1 := by
    first
    | exact (HW l).W_s K 1 LL hG
    | exact (HW l).hs K 1 LL hG
    | exact (HW l).s_eq K 1 LL hG
    | exact (HW l).W_s
    | rfl
  obtain ⟨-, ⟨π', E, hr, -⟩, -⟩ := h9 hs (by rw [hpe]; exact hl)
  refine ⟨π', E, ?_⟩
  convert hr using 2 <;> first | rfl | (simp only [eK, sK, hpe]) | (unfold eK sK; simp [hpe])

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem qpf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have h : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => PD.Fil_anti a hx
  intro x hx
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) y, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]

theorem qpf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := by
  unfold FildR
  exact inf_le_inf_left _ (qpf_filV_succ_le PD a)

theorem qpf_isJumpV_iff_pos (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    IsJumpV PD ρ τ a ↔ 0 < multV PD ρ τ a := by
  have hle := qpf_fildR_succ_le PD ρ τ a
  haveI := hfin
  haveI : Module.Finite LL ↥(FildR PD ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
      (Submodule.inclusion_injective _)
  unfold IsJumpV multV
  constructor
  · intro hne
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
    omega
  · intro hpos heq
    rw [heq] at hpos
    simp at hpos

theorem qpf_multV_nonneg (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ) :
    0 ≤ multV PD ρ τ a := by
  by_cases h : FildR PD ρ τ (a + 1) = FildR PD ρ τ a
  · unfold multV
    rw [h]
    simp
  · exact le_of_lt ((qpf_isJumpV_iff_pos PD ρ τ hfin a).1 h)

end Gen

theorem quotient_jumps_subset (D : D7) (h8 : adm8 D) (h11 : adm11 D) : quotR D := by
  unfold quotR
  intro l _ hl2 K LL hG
  unfold quotA
  intro T₁ T₂ F hc1 hc2 hon τ X hJ a ha
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    have hint : IsIntegral ℚ_[l] c := Algebra.IsIntegral.isIntegral c
    have halg : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 hint.isAlgebraic
    have hinj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
      exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    obtain ⟨y, hy, hyc⟩ : ∃ y ≠ (0 : ℤ_[l]), IsIntegral ℤ_[l] (y • c) := by
      exact IsAlgebraic.exists_integral_multiple halg
    refine ⟨algebraMap ℤ_[l] ↥(OL LL) y, ?_, ⟨y • c, hyc⟩, ?_⟩
    · rw [← IsScalarTower.algebraMap_apply]
      exact fun h => hy (hinj (h.trans (map_zero _).symm))
    · rw [← IsScalarTower.algebraMap_apply]
      change _ = y • c
      rw [Algebra.smul_def]
  have hses : IsSESLat (Qp := ℚ_[l]) (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F := by
    refine ⟨(LinearMap.ker F.f).injective_subtype, Formalism.MainNotions.LiftingTheory.lker_surj F hon, hon,
      fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, ?_⟩, fun y hy => hy⟩
    rintro ⟨y, rfl⟩
    exact LinearMap.mem_ker.1 y.2
  obtain ⟨-, -, hmult⟩ := h11 l K LL _ T₁ T₂ (Formalism.MainNotions.LiftingTheory.lker_ι F hon hden) F hses hc1
  apply hJ
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₂).2 τ).1] at ha
  rw [qpf_isJumpV_iff_pos _ _ τ ((h8 l K LL T₁).2 τ).1, hmult τ a]
  have h0 := qpf_multV_nonneg _ _ τ ((h8 l K LL (Formalism.MainNotions.LiftingTheory.lker_T₀ F hon hden)).2 τ).1 a
  omega

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2T

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" x:max => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)

theorem u2ringPfT_natCast_unit [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {s : ℕ} (hs1 : 1 ≤ s) (hsp : s < p) : IsUnit (s : O) := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  by_contra h
  have hm : (s : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ p] at hm
  exact absurd (Nat.le_of_dvd (by omega) hm) (by omega)

theorem u2ringPfT_deriv [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) {x y : O}
    (hxm : x ∈ IsLocalRing.maximalIdeal O) (hx1 : (1 + x) ^ PD.p = 1) (hx0 : x ≠ 0)
    (hy : (mkI x) (π' c) = (mkI x) (PowerSeries.C y)) :
    ∃ ε : O, IsUnit ε ∧ y * (E c).derivative.eval y = (PD.p : O) * ε := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, -, -⟩ := hR
  set p := PD.p with hpdef
  have hp2 : 2 ≤ p := PD.hp.two_le
  set π := π' c with hπdef
  set u := (w : LetA O n) c with hudef
  have hu : IsUnit u := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  have hπu : π = u * PowerSeries.X ^ s' := by rw [hπdef, hw]; rfl
  set wq := (w₁ : LetA O n) c with hwqdef
  have hwq : IsUnit wq := w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  set Ec := E c with hEcdef
  have hQ : W.q₀ = wq * Polynomial.aeval π Ec := congrFun hq c
  set D := PowerSeries.derivative (R := O) with hD
  obtain ⟨uv, huv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm u
  obtain ⟨duv, hduv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D u)
  obtain ⟨wv, hwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm wq
  obtain ⟨dwv, hdwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D wq)
  obtain ⟨qv, hqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm W.q₀
  obtain ⟨dqv, hdqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D W.q₀)
  have hwvu : IsUnit wv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv
  have huvu : IsUnit uv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hu) huv

  have hqv0 : qv = 0 := by
    have h1 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) W.q₀_def
    have e1 : (mkI x) (PowerSeries.X * W.q₀) = (mkI x) (PowerSeries.C (x * qv)) := by
      simp only [map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv]
    have e2 : (mkI x) ((1 + PowerSeries.X) ^ p - 1) = (mkI x) (PowerSeries.C ((1 + x) ^ p - 1)) := by
      simp only [map_sub, map_pow, map_add (f := _), map_one, DualFramesAlt.eigenRingInvariants.mk_X]
    rw [e1, e2, hx1, sub_self] at h1
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h1)).resolve_left hx0

  have hyu : y = uv * x ^ s' := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    rw [← hy]
    simp only [hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X]
  have hEy : Ec.eval y = 0 := by
    have h4 : (mkI x) W.q₀ = (mkI x) (PowerSeries.C (wv * Ec.eval y)) := by
      simp only [hQ, map_mul, hwv, u2ringPfE_mk_aeval hy]
    rw [hqv, hqv0] at h4
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h4).symm).resolve_left hwvu.ne_zero

  have hdX : D PowerSeries.X = 1 := PowerSeries.derivative_X
  have hd1 := congrArg D W.q₀_def
  rw [Derivation.leibniz, map_sub, Derivation.leibniz_pow, Derivation.map_one_eq_zero, sub_zero, map_add (f := _),
    Derivation.map_one_eq_zero, zero_add, hdX] at hd1
  have hd2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hd1
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul, map_add (f := _), map_mul, map_pow, map_natCast,
    DualFramesAlt.eigenRingInvariants.mk_X, hqv, hdqv, hqv0, map_one] at hd2
  have hDπ : D π = u * ((s' : PowerSeries O) * PowerSeries.X ^ (s' - 1)) + PowerSeries.X ^ s' * D u := by
    rw [hπu, Derivation.leibniz, Derivation.leibniz_pow, hdX]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
    try ring
  have hdq := congrArg D hQ
  rw [Derivation.leibniz, Derivation.map_aeval, hDπ] at hdq
  have hdq2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hdq
  simp only [smul_eq_mul, map_add (f := _), map_mul, map_pow, map_natCast, DualFramesAlt.eigenRingInvariants.mk_X, hdqv, hwv, hduv, huv,
    u2ringPfE_mk_aeval hy, hEy] at hdq2

  have e1 : x * dqv = (p : O) * (1 + x) ^ (p - 1) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add (f := _), map_one, map_natCast]
    simp only [map_zero, add_zero] at hd2
    linear_combination hd2
  have e2 : dqv = wv * ((Ec.derivative.eval y) * (uv * ((s' : O) * x ^ (s' - 1)) + x ^ s' * duv)) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add (f := _), map_natCast]
    simp only [map_zero, zero_mul, add_zero] at hdq2
    linear_combination hdq2
  have hs'u : IsUnit (s' : O) := u2ringPfT_natCast_unit p hpm hs (by
    have : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, zero_mul] at hes; omega
      · exact h
    have : s' ≤ e * s' := Nat.le_mul_of_pos_left s' this
    omega)
  have hD0 : IsUnit (wv * (uv * (s' : O) + x * duv)) := by
    refine hwvu.mul ?_
    by_contra hn
    have hm : uv * (s' : O) + x * duv ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hm2 : uv * (s' : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right duv _ hxm)
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 hm2 (huvu.mul hs'u)
  have h1xe : (1 + x) * (1 + x) ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hx1]
  have h1x : IsUnit (1 + x) := ⟨⟨1 + x, (1 + x) ^ (p - 1), h1xe, by rw [mul_comm]; exact h1xe⟩, rfl⟩
  obtain ⟨Du, hDu⟩ := hD0
  refine ⟨uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O), (huvu.mul (h1x.pow _)).mul (Du⁻¹).isUnit, ?_⟩
  have key : y * Ec.derivative.eval y * (wv * (uv * (s' : O) + x * duv)) = (p : O) * (uv * (1 + x) ^ (p - 1)) := by
    obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at e2
    linear_combination (Ec.derivative.eval y * (wv * (uv * ((s'' + 1 : ℕ) : O) + x * duv))) * hyu -
      (uv * x) * e2 + uv * e1
  have hDuinv : ((Du : Oˣ) : O) * ((Du⁻¹ : Oˣ) : O) = 1 := Units.mul_inv Du
  rw [hDu] at hDuinv
  calc y * Ec.derivative.eval y = y * Ec.derivative.eval y * ((wv * (uv * (s' : O) + x * duv)) *
        ((Du⁻¹ : Oˣ) : O)) := by rw [hDuinv, mul_one]
    _ = (p : O) * (uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O)) := by rw [← mul_assoc, key]; ring

theorem u2ringPfT_split [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) (ζ : O)
    (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : PD.p ≠ 2) (hι : Function.Injective (algebraMap O LL))
    (hRv : ∀ x : LL, 0 ≤ v x ↔ ∃ a : O, algebraMap O LL a = x) :
    ∃ (a : O) (r : Fin e → O), IsUnit a ∧ (∀ j, r j ∈ IsLocalRing.maximalIdeal O) ∧
      E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
        (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨a, r, ha, hrm, hsplit, hpt⟩ := u2ringPfS_split W hR hs hes hpm c ζ hζ
  refine ⟨a, r, ha, hrm, hsplit, ?_⟩
  intro j w₀ hw₀ t ht
  obtain ⟨x, hxm, hx1, hx0, hxy⟩ := hpt j
  obtain ⟨ε, hε, hyE⟩ := u2ringPfT_deriv W hR hs hes hpm c hxm hx1 hx0 hxy
  have hder : (E c).derivative.eval (r j) = a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') := by
    rw [hsplit, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_prod_finset, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp [Polynomial.eval_prod]
    · intro b _ hb
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hb h.symm, Finset.mem_univ j⟩) (by simp)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hder] at hyE
  have hxt : (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) - 1 = ((PD.p : ℕ) : O) * (w₀ * ε) := by
    linear_combination w₀ * hyE
  obtain ⟨ε', hε', he'⟩ := gradNPf_lte v (algebraMap O LL) hι hRv PD.p hp2 W.v_l _ (w₀ * ε) (hw₀.mul hε) hxt t
    (by omega)
  intro h1
  rw [h1, sub_self] at he'
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
  exact (mul_ne_zero (pow_ne_zero _ hp0) hε'.ne_zero) he'.symm

end U2T

end Formalism.MainNotions.N.Ln34
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLG

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V']

def Bdd (F : ℤ → V') (m₀ : ℤ) : Prop := ∀ i < m₀, F i = 0

theorem serMul_eq_sum (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) (M : ℕ)
    (hM : (i - m₀).toNat + 1 ≤ M) :
    serMul P F i = ∑ k ∈ Finset.range M, PowerSeries.coeff k P • F (i - k) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hkM
  apply hk
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_bdd (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) : Bdd (serMul P F) m₀ := by
  intro i hi
  unfold serMul
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_serMul (P Q : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) :
    serMul P (serMul Q F) i = serMul (P * Q) F i := by
  set N := (i - m₀).toNat + 1 with hN
  rw [serMul_eq_sum P (serMul_bdd Q hF) i N le_rfl, serMul_eq_sum (P * Q) hF i N le_rfl]
  have hL : ∀ k ∈ Finset.range N, PowerSeries.coeff k P • serMul Q F (i - k) =
      ∑ j ∈ Finset.range (N - k), (PowerSeries.coeff k P * PowerSeries.coeff j Q) • F (i - (k + j : ℕ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [serMul_eq_sum Q hF (i - k) (N - k) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ s ∈ Finset.range N, PowerSeries.coeff s (P * Q) • F (i - s) =
      ∑ k ∈ Finset.Ico 0 (s + 1), (PowerSeries.coeff k P * PowerSeries.coeff (s - k) Q) • F (i - s) := by
    intro s _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl hR, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

theorem serMul_X_pow (h : ℕ) (F : ℤ → V') (i : ℤ) :
    serMul (PowerSeries.X ^ h : PowerSeries LL) F i = F (i - h) := by
  unfold serMul
  rw [finsum_eq_single _ h (fun k hk => by rw [PowerSeries.coeff_X_pow, if_neg hk, zero_smul])]
  rw [PowerSeries.coeff_X_pow, if_pos rfl, one_smul]

theorem serMul_rescale (u : LL) (hu : u ≠ 0) (P : PowerSeries LL) (F : ℤ → V') (i : ℤ) :
    u ^ i • serMul P F i = serMul (PowerSeries.rescale u P) (fun j => u ^ j • F j) i := by
  unfold serMul
  rw [smul_finsum]
  refine finsum_congr (fun k => ?_)
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show u ^ i = u ^ (k : ℤ) * u ^ (i - k) by rw [← zpow_add₀ hu]; ring_nf, zpow_natCast]
  ring

end Formalism.MainNotions.N.Ln34.MLG

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def Phi (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T) :
    (Fin r → LL) →ₗ[LL] T.V ⊗[Qp] BdR where
  toFun d := ∑ k, d k • valAt W T c ζ (rep k)
  map_add' d d' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a d := by simp [Finset.smul_sum, smul_smul]

theorem Phi_apply (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T)
    (d : Fin r → LL) : Phi W T c ζ rep d = ∑ k, d k • valAt W T c ζ (rep k) := rfl

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
