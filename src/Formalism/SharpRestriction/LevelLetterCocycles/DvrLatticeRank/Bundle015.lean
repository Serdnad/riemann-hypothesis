module

import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpPowSubOne
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Zero

open PowerSeries

variable {LL : Type} [Field LL]

theorem framepf_exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  apply Formalism.MainNotions.N.Pv.LocalLengthBound.exp_pow_sub_one <;> assumption

end Zero

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)


open PowerSeries in
theorem framepf_lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  apply Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple <;> assumption

theorem framepf_Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [Formalism.BasicNotions.LocWach.Q, hs]

theorem framepf_Q_at (hs : W.s = 1) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  rw [framepf_Q_eq_q W hs, hu]
  refine ⟨by simp, ?_⟩
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * u) = PowerSeries.coeff 0 u :=
    PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu0

end Local

theorem framepf_pt_prim (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : IsPrimitiveRoot ζ l := by
  obtain ⟨τs, ⟨-, hroot⟩, -⟩ := hpt
  have hpow : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rwa [zero_add, (D.loc l).ζQ_zero] at h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show _ ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    refine (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _) ?_
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one]
    exact hpow
  set y : Ks K 1 := ⟨_, hmem⟩ with hydef
  have hyζ : τs y = ζ := hroot y rfl
  have hy1 : y ^ l = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hpow
  have hy2 : y ≠ 1 := by
    intro h
    apply (D.loc l).ζQ_one
    have h' := congrArg Subtype.val h
    exact h'
  have hprim : IsPrimitiveRoot y l := by
    have ho := orderOf_eq_prime hy1 hy2
    have h0 := IsPrimitiveRoot.orderOf y
    rwa [ho] at h0
  rw [← hyζ]
  exact hprim.map_of_injective τs.injective

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem alpha_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt)
    (x : LA W T π' c) (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hxS : x ∈ NLset W T Pt π' Eπ h' c)
    (y0 : W.DD T) (hy0 : y0 ∈ LamPS W T Eπ h' c) (hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0) :
    y0 ∈ W.N T := by
  obtain ⟨h1, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
  have hE2 : Eπ ^ h' • (Eπ ^ h' • y0) ∈ W.N T := Eπ_φspan W T Eπ h' c hww hQ h5a h1
  have eEQ : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
    rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
  refine hexp c y0 ((mem_DelS W T y0).2 h2) ((mem_letS W T c y0).2 h3) ⟨2 * h', ?_⟩ ?_
  · rw [hQ, mul_pow, mul_smul, show Eπ ^ (2 * h') = Eπ ^ h' * Eπ ^ h' by rw [two_mul, pow_add],
      mul_smul]
    exact Submodule.smul_mem _ _ hE2
  · intro ζ τ hPt k hk i
    obtain ⟨hc0, hc1⟩ := levQ_pt W hs c ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
    obtain ⟨m, a, z, hrep, hfil⟩ := hxS
    have e1 : W.Q ^ k • (Eπ ^ h' • y0) = (w' ^ h' * W.Q ^ h') • (W.Q ^ k • y0) := by
      rw [eEQ, smul_smul, smul_smul, mul_comm (W.Q ^ k)]
    have hQΛ : W.Q ^ k • (Eπ ^ h' • y0) ∈ W.N T := e1 ▸ Submodule.smul_mem _ _ hk
    have hF : ∀ i' : ℤ, W.levN T c ζ ⟨_, hQΛ⟩ i' ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) + h' - i') := by
      intro i'
      rcases lt_or_ge i' ((k : ℤ) + 4 * h') with hi | hi
      · rw [(hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx y0 hy0 hα m a z hrep k hQΛ i' hi]
        refine nsmul_mem ?_ _
        have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i))
          (FilC_mono_shift T τ _) (W.lev c ζ (W.Q ^ k)) k
          (by rw [map_pow]; exact pow_vanish' _ hc0 k) _ (hfil τ ζ hPt) i'
        convert this using 2
        ring
      · have h0 := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hQΛ⟩ i')).2
        exact FilC_anti T τ (by omega) (FilC_top T h' τ (hjmp τ) _ h0)
    have hsub : (⟨_, hQΛ⟩ : ↥(W.N T)) = (w' ^ h' * W.Q ^ h') • (⟨_, hk⟩ : ↥(W.N T)) :=
      Subtype.ext e1
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T c ζ ⟨_, hk⟩
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
    have hw0 : PowerSeries.constantCoeff (W.lev c ζ w') ≠ 0 := by
      intro h
      have hw : PowerSeries.constantCoeff (W.lev c ζ w') *
          PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
        rw [← map_mul, ← map_mul, hww, map_one, map_one]
      rw [h, zero_mul] at hw
      exact zero_ne_one hw
    have hB0 : PowerSeries.constantCoeff B' ≠ 0 := by
      rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc1
      exact hc1
    have eg : W.lev c ζ (w' ^ h' * W.Q ^ h') =
        PowerSeries.X ^ h' * (W.lev c ζ w' ^ h' * B' ^ h') := by
      rw [map_mul, map_pow, map_pow, hB', mul_pow]
      ring
    refine serMul_inv (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) (FilC_mono_shift T τ _)
      (W.lev c ζ (w' ^ h' * W.Q ^ h')) h' ?_ ?_ (W.levN T c ζ ⟨_, hk⟩) m₀ hm₀ ?_ i
    · intro j hj
      rw [eg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    · rw [eg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow]
      exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hB0)
    · intro i''
      rw [← levN_eq_serMul, ← hsub]
      have := hF (i'' + h')
      convert this using 2
      ring

end Core

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

theorem exponent_recursion_holds : ExpansionFormHypothesis := fun D HW F Cm _ _ _ hA hd hr =>
  CrystallineExponents.exponent_recursion_of_dimension D HW F Cm hA.1 hA.2.2.2.2.2.2.2.2.2.2.1 fun l _ K LL hG T hT c τ =>
    ((hr l K LL hG T hT c).trans (hd l K LL ⟨1, hG⟩ T hT τ).symm).le

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

def LV (K : ℕ) (x : W.DD T) : T.V ⊗[Qp] BdR :=
  open Classical in
  if h : W.Q ^ K • W.φD T x ∈ W.N T then W.levN T c ζ ⟨_, h⟩ K else 0

theorem LV_eq (K : ℕ) (x : W.DD T) (h : W.Q ^ K • W.φD T x ∈ W.N T) :
    LV W T c ζ K x = W.levN T c ζ ⟨_, h⟩ K := by
  unfold LV
  rw [dite_eq_left h]

theorem LV_add (K : ℕ) (x y : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hy : W.Q ^ K • W.φD T y ∈ W.N T) : LV W T c ζ K (x + y) = LV W T c ζ K x + LV W T c ζ K y := by
  have hxy : W.Q ^ K • W.φD T (x + y) ∈ W.N T := by
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ hx hy
  rw [LV_eq W T c ζ K _ hxy, LV_eq W T c ζ K _ hx, LV_eq W T c ζ K _ hy]
  rw [show (⟨_, hxy⟩ : ↥(W.N T)) = ⟨_, hx⟩ + ⟨_, hy⟩ from
    Subtype.ext (by simp only [map_add (f := _), smul_add, Submodule.coe_add]), map_add (f := _)]
  rfl

theorem LV_smulA (K : ℕ) (a : LetA O n) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hv : ∀ j : ℤ, j < K → W.levN T c ζ ⟨_, hx⟩ j = 0) :
    W.Q ^ K • W.φD T (a • x) ∈ W.N T ∧
      LV W T c ζ K (a • x) = PowerSeries.constantCoeff (W.lev c ζ (W.φA a)) • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (a • x) = W.φA a • (W.Q ^ K • W.φD T x) := by
    rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, smul_comm]
  have hax : W.Q ^ K • W.φD T (a • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hax, ?_⟩
  rw [LV_eq W T c ζ K _ hax, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hax⟩ : ↥(W.N T)) = W.φA a • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ K hv K 1 (by omega), Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem LV_smulO (K : ℕ) (o : O) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T) :
    W.Q ^ K • W.φD T (o • x) ∈ W.N T ∧
      LV W T c ζ K (o • x) = algebraMap O LL o • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (o • x) = algebraMap O (LetA O n) o • (W.Q ^ K • W.φD T x) := by
    rw [map_smul, smul_comm, algebraMap_smul]
  have hox : W.Q ^ K • W.φD T (o • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hox, ?_⟩
  rw [LV_eq W T c ζ K _ hox, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hox⟩ : ↥(W.N T)) = algebraMap O (LetA O n) o • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  have hC : algebraMap O (PowerSeries LL) o = PowerSeries.C (algebraMap O LL o) := by
    rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
    rfl
  rw [hs, levN_eq_serMul, AlgHom.commutes, hC]
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_C, if_neg hj, zero_smul]

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_val (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : W.DD T) (hxN : x ∈ W.N T) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) :
    W.levN T c ζ ⟨_, hk⟩ k = PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ k • valAt W T c ζ x := by
  classical
  have hex : ∃ k, W.Q ^ k • W.φD T x ∈ W.N T := ⟨k, hk⟩
  unfold valAt
  rw [dite_eq_left hex]
  have hk0 : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hk0m := Nat.find_spec hex
  have hv : ∀ j : ℤ, j < (Nat.find hex : ℤ) → W.levN T c ζ ⟨_, hk0m⟩ j = 0 :=
    fun j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hxN⟩ _ hk0m j).2 hj
  have hs : (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ (k - Nat.find hex) • (⟨_, hk0m⟩ : ↥(W.N T)) :=
    Subtype.ext (by
      show W.Q ^ k • W.φD T x = W.Q ^ (k - Nat.find hex) • W.Q ^ Nat.find hex • W.φD T x
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hk0])
  obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hB0 : PowerSeries.constantCoeff B' = PowerSeries.coeff 1 (W.lev c ζ W.Q) := by
    rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ _ hv k (k - Nat.find hex + 1) (by omega),
    Finset.sum_eq_single (k - Nat.find hex)]
  · have e1 : (k : ℤ) - ((k - Nat.find hex : ℕ) : ℤ) = (Nat.find hex : ℤ) := by
      rw [Nat.cast_sub hk0]
      ring
    have hcoef : PowerSeries.coeff (k - Nat.find hex) ((W.lev c ζ W.Q) ^ (k - Nat.find hex)) =
        PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ (k - Nat.find hex) := by
      rw [hB', mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, map_pow, hcoef, smul_smul, ← pow_sub₀ _ hc1 hk0]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [map_pow, pow_vanish' _ hc0 _ j h, zero_smul]
    · rw [hv _ (by omega), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Core2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

theorem beta_core (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) {w w' : LetA O n}
    (hww : w' * w = 1) (hQ : W.Q = w * Eπ) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) (hyN : y ∈ W.N T) (x : LA W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hβ : β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx) :
    x ∈ NLset W T Pt π' Eπ h' c := by
  obtain ⟨m, a, z, hz, heq⟩ := range_rep W T π' c _ hx
  have hrep : IsRepL W T π' Eπ h' c x a z := ⟨hz, heq⟩
  refine ⟨m, a, z, hrep, ?_⟩
  intro τ ζ hPt i
  have hzN : ∀ j, z j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hz j)).1
  have hα := (hfr.1 T hcry hjmp).2.2.2.1 y hy x hx hβ
  have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
  rcases lt_or_ge i (4 * h') with hi | hi
  · have hpy : ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ W.N T := Submodule.smul_of_tower_mem _ _ hyN
    have hk : W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) ∈ W.N T := by
      rw [pow_zero, one_smul]
      exact Submodule.smul_mem _ _ hpy
    have hexp := (hfr.1 T hcry hjmp).2.2.2.2.2.2.2.2 τ ζ hPt x hx _ _ hα m a z hrep 0 hk i
      (by simpa using hi)
    have hl1 : W.lev c ζ (W.Q ^ 0) = 1 := by rw [pow_zero, map_one]
    rw [hl1, serMul_one] at hexp
    have hsub : (⟨_, hk⟩ : ↥(W.N T)) = Eπ ^ h' • (⟨_, hpy⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        show W.Q ^ 0 • (Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)) =
          Eπ ^ h' • (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        rw [pow_zero, one_smul])
    have hL : W.levN T c ζ ⟨_, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((h' : ℤ) - i) := by
      rw [hsub, levN_eq_serMul]
      have := serMul_mem (fun i => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (0 - i)) (FilC_mono_shift T τ 0)
        (W.lev c ζ (Eπ ^ h')) h' (by rw [map_pow]; exact pow_vanish' _ hcE h') _
        (fun i => by
          have := (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hpy⟩ i)).2
          simpa using this) i
      convert this using 2
      ring
    rw [hexp, ← Nat.cast_smul_eq_nsmul LL] at hL
    exact (Submodule.smul_mem_iff _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ (p_ne_zero W))).1 hL
  · exact FilC_anti T τ (by omega) (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))

theorem JLA_le (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ)
    (j : ℕ) (hj : j ≤ M) : JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c j := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
  obtain ⟨m, a, z, hz, rfl⟩ := range_rep W T π' c v hv
  have hb : π' ^ (M - j) * Eπ ^ (3 * h') ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem hπΔ _) (W.AΔ.pow_mem hEΔ _)
  refine ⟨smulLA W T π' c (π' ^ (M - j) * Eπ ^ (3 * h')) (∑ k, algebraMap (LetA O n) W.EE
    ((letE c : LetA O n) * (a k : LetA O n)) ⊗ₜ mkL W T π' c (z k) (hz k)), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨m, fun k => ⟨Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * a k),
      W.AΔ.mul_mem (W.AΔ.pow_mem hEΔ _) (W.AΔ.mul_mem hb (a k).2)⟩, z, ⟨hz, ?_⟩, ?_⟩
    · rw [smulLA_rep, smulLA_rep]
    · intro τ ζ hPt i
      have hzN : ∀ k, z k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hz k)).1
      have hcE := levE_zero W Eπ c hs hww hQ ζ (hpt ζ τ hPt).1 (hpt ζ τ hPt).2
      rcases lt_or_ge i (4 * h') with hi | hi
      · unfold expS serC
        refine Submodule.sum_mem _ fun k _ => ?_
        split_ifs with h0
        · have e : Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) * (a k : LetA O n)) =
              Eπ ^ (4 * h') * (π' ^ (M - j) * a k) := by ring
          show PowerSeries.coeff i.toNat (W.lev c ζ (Eπ ^ h' * ((π' ^ (M - j) * Eπ ^ (3 * h')) *
            (a k : LetA O n)))) • valAt W T c ζ (z k) ∈ _
          rw [e, map_mul, map_pow, pow_vanish _ hcE _ _ _ (by omega), zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · exact FilC_anti T τ (by omega)
          (ιDi_le_top W T h' c hp4 hPt (hjmp τ) (expS_mem W T c hp4 hPt _ z hzN i))
  · show smulLA W T π' c (π' ^ j) (smulLA W T π' c _ _) = _
    rw [smulLA_smulLA, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]

end Core2

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end
