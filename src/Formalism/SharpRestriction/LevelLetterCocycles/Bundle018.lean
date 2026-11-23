module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.LengthRestrictNat
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section CoreW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem cancel_unit_mul_uniformizer_pow {w : (LetA O n)ˣ} {k : ℕ} {a b : LetA O n}
    (h : (w : LetA O n) * letπ ^ k * a = (w : LetA O n) * letπ ^ k * b) : a = b := by
  unfold letπ at h
  have h' : (fun _ => PowerSeries.X) ^ k * a = (fun _ => PowerSeries.X) ^ k * b := by
    have := congrArg (fun x => (↑w⁻¹ : LetA O n) * x) h
    simpa [← mul_assoc, Units.inv_mul] using this
  funext i
  have hi := congrFun h' i
  simp only [Pi.mul_apply, Pi.pow_apply] at hi
  ext m
  have hm := congrArg (PowerSeries.coeff (m + k)) hi
  rwa [mul_comm, PowerSeries.coeff_mul_X_pow, mul_comm, PowerSeries.coeff_mul_X_pow] at hm

theorem pi0Core_of (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (h1 : W.π₀ ∈ W.AΔ)
    (h3 : W.π₀ = (w : LetA O n) * letπ ^ k) : Pi0LatticeCondition W := by
  intro g
  obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.gamma_X_eq W g
  obtain ⟨Uc, hUc⟩ : ∃ Uc : LetA O n,
      Uc = fun _ => PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t := ⟨_, rfl⟩
  have hπ : W.γA g letπ = letπ * Uc := by
    funext i
    rw [hUc]
    show W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t)
    exact ht
  obtain ⟨u, hu⟩ : ∃ u : LetA O n, u = (↑w⁻¹ : LetA O n) * W.γA g (w : LetA O n) * Uc ^ k :=
    ⟨_, rfl⟩
  have heq : W.γA g W.π₀ = W.π₀ * u := by
    rw [h3, map_mul, map_pow, hπ, hu,
      show (↑w : LetA O n) * letπ ^ k * (↑w⁻¹ * W.γA g ↑w * Uc ^ k) =
        (↑w * ↑w⁻¹) * (W.γA g ↑w * (letπ * Uc) ^ k) by ring,
      Units.mul_inv, one_mul]
  refine ⟨u, ?_, heq⟩
  have hmem : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  show ∀ δ ∈ W.DelF, W.γA δ u = u
  intro δ hδ
  have e1 : W.γA δ (W.γA g W.π₀) = W.γA g W.π₀ := by
    rw [Formalism.MainNotions.LiftingTheory.gammaA_comm W δ g, hmem δ hδ]
  rw [heq, map_mul, hmem δ hδ, h3] at e1
  exact cancel_unit_mul_uniformizer_pow e1

end CoreW

theorem finrank_K0_eq_one_of_le_Kur {l : ℕ} [Fact l.Prime] {K : FinExt l} (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    Module.finrank ↥(K0 K) ↥K.1 = 1 := by
  unfold K0
  rw [finrank_eq_one_iff_of_nonzero' (1 : ↥K.1) one_ne_zero]
  intro x
  refine ⟨⟨(x : Om l), IntermediateField.mem_inf.mpr ⟨x.2, hK x.2⟩⟩, ?_⟩
  first
    | exact Subtype.ext (mul_one _)
    | exact Subtype.ext (by simp)
    | rfl

theorem ring_condition_uniformizer_polynomial (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL h.2.2) 1 (((D.loc l).PD K).p - 1) ((HW l).W K 1 LL h.2.2).π₀
      (fun _ => Polynomial.X + Polynomial.C ((((D.loc l).PD K).p : ℕ) : ↥(OL LL))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9W := h9 l K 1 LL h.2.2
  have hp := h9W _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL h.2.2))
  refine ((hp ?_ ?_).2.2 ?_).1
  · exact (HW l).W_s K 1 LL h.2.2
  · rw [(D.loc l).PD_p K]
    exact h.2.1
  · exact finrank_K0_eq_one_of_le_Kur h.1

theorem gamma_uniformizer_divisible_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : UniformiserGammaTheorem D HW F := by
  intro h9 l _ K LL h _
  obtain ⟨h1, -, ⟨w, hw⟩, -⟩ := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  exact pi0Core_of _ w _ h1 hw

end Formalism.MainNotions.UnusedSlot80
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section DStab

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smul' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem rToolMod_geom (a : LetA O n) (m : ℕ) : ∃ g : LetA O n, (1 + a) ^ m = 1 + a * g := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨1 + g + a * g, by rw [pow_succ, hg]; ring⟩

theorem rToolMod_unit (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (t : LetA O n) (m : ℕ) : IsUnit ((1 + W.π₀ * t) ^ m) := by
  obtain ⟨w, hw⟩ := hπ
  have hp : 2 ≤ PD.p := by
    by_contra h
    have hv := W.v_l
    rcases (show PD.p = 0 ∨ PD.p = 1 by omega) with h0 | h0 <;> rw [h0] at hv
    · rw [Nat.cast_zero, AddValuation.map_zero] at hv
      exact WithTop.top_ne_coe (show (⊤ : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) from hv)
    · rw [Nat.cast_one, AddValuation.map_one] at hv
      have h01 : ((0 : ℚ) : WithTop ℚ) = ((1 : ℚ) : WithTop ℚ) := hv
      exact absurd (WithTop.coe_inj.mp h01) (by norm_num)
  have hp1 : PD.p - 1 ≠ 0 := by omega
  refine IsUnit.pow m ?_
  refine Pi.isUnit_iff.mpr fun i => ?_
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  simp [hw, letπ, zero_pow hp1]

theorem rToolMod_qi_q (hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (m : ℕ)
    (x : W.DD T) :
    Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • x) = x := by
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ m) x, smul_smul, map_pow, ← mul_pow,
    Ring.inverse_mul_cancel _ hqU, one_pow, one_smul]

theorem rToolMod_dStab [NeZero n] (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : DerivationPreservesQLattice W := by
  unfold DerivationPreservesQLattice
  intro hA T' hT i k x hx
  obtain ⟨hbij, hs, hp2⟩ := hA
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hbij).finrank_eq, Module.finrank_self]
  obtain ⟨-, -, h9⟩ := hP9 T' hT hs hp2
  obtain ⟨hring, hmod⟩ := h9 hfin
  obtain ⟨-, hmod2⟩ := hmod
  obtain ⟨hπΔ, -, ⟨w₁, hw₁⟩, -, -, -, ⟨w₂, hw₂⟩, -⟩ := hring
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hπΔ
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp]
  have hγπ : W.γA W.gam W.π₀ = W.π₀ + (w₂ : LetA O n) * W.π₀ * Formalism.MainNotions.LiftingTheory.qp W := by
    rw [← hEat, ← hw₂]; ring
  have hγq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      Formalism.MainNotions.LiftingTheory.qp W * (1 + W.π₀ * (w₂ : LetA O n)) := by
    have e1 : W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
    rw [e1, hγπ]
    simp only [Formalism.MainNotions.LiftingTheory.qp]
    ring
  have hΔq : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
    intro δ hδ
    simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, hΔπ δ hδ]
  have ha : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw₁, map_mul, map_pow]
    exact (w₁.isUnit.map _).mul (W.EE_π.pow _)
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
    haveI := W.EE_complete
    have hI : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        Ideal.span {((PD.p : ℕ) : W.EE)} := Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    have hJ : ((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) ∈
        (⊥ : Ideal W.EE).jacobson := by
      first
        | exact IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
        | exact HenselianRing.jac (I := Ideal.span {((PD.p : ℕ) : W.EE)}) hI
    have h1 := Ideal.mem_jacobson_bot.mp hJ 1
    have hinv := Ring.mul_inverse_cancel _ ha
    have h2 : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) = algebraMap (LetA O n) W.EE W.π₀ *
        (((PD.p : ℕ) : W.EE) * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * 1 + 1) := by
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast]
      linear_combination (-((PD.p : ℕ) : W.EE)) * hinv
    rw [h2]; exact ha.mul h1
  obtain ⟨e, he⟩ : ∃ e, e = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := ⟨_, rfl⟩
  have hcan1 : ∀ z : W.DD T', W.π₀ • (e • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀, smul_smul, Ring.mul_inverse_cancel _ ha, one_smul]
  have hcan2 : ∀ z : W.DD T', e • (W.π₀ • z) = z := by
    intro z
    rw [he, ← algebraMap_smul W.EE W.π₀ z, smul_smul, Ring.inverse_mul_cancel _ ha, one_smul]
  have hinj : ∀ z₁ z₂ : W.DD T', W.π₀ • z₁ = W.π₀ • z₂ → z₁ = z₂ := by
    intro z₁ z₂ h; rw [← hcan2 z₁, h, hcan2]
  have hcomm : ∀ (b : LetA O n) (z : W.DD T'), b • (e • z) = e • (b • z) := by
    intro b z
    rw [← algebraMap_smul W.EE b (e • z), ← algebraMap_smul W.EE b z, smul_smul, smul_smul, mul_comm]
  have hγE : ∀ δ ∈ W.DelF, W.γE δ e = e := by
    intro δ hδ
    have h3 : W.γE δ (algebraMap (LetA O n) W.EE W.π₀) = algebraMap (LetA O n) W.EE W.π₀ := by
      rw [W.γE_ext]; exact congrArg (algebraMap (LetA O n) W.EE) (hΔπ δ hδ)
    rw [he]
    calc W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀))
        = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) *
          (algebraMap (LetA O n) W.EE W.π₀ * Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)) := by
          rw [Ring.mul_inverse_cancel _ ha, mul_one]
      _ = W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) * algebraMap (LetA O n) W.EE W.π₀) *
          Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by rw [map_mul, h3]; ring
      _ = Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) := by
          rw [Ring.inverse_mul_cancel _ ha, map_one, one_mul]
  have hγsm : ∀ (g : W.Gam) (b : LetA O n) (z : W.DD T'),
      W.γD T' g (b • z) = W.γA g b • W.γD T' g z := γD_smul' W T'
  have hdOp : ∀ z, Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' z = e • (W.γD T' W.gam z - z) := fun z => by rw [he]; rfl
  have hγy : ∀ (m : ℕ) (z : W.DD T'), W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ m • z) =
      (1 + W.π₀ * (w₂ : LetA O n)) ^ m • (Formalism.MainNotions.LiftingTheory.qp W ^ m • W.γD T' W.gam z) := by
    intro m z
    rw [hγsm, map_pow, hγq, mul_pow, smul_smul, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ m)]
  obtain ⟨⟨hEx, hΔx⟩, hq⟩ := hx
  have hγE_i : W.γA W.gam (letE i : LetA O n) = letE i := by
    funext j
    show W.γ₀ W.gam ((letE i : LetA O n) j) = (letE i : LetA O n) j
    simp only [letE, Pi.single_apply]
    split_ifs <;> simp
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN Formalism.MainNotions.CrystallineLiftingInputs.DL
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hEγ : (letE i : LetA O n) • W.γD T' W.gam x = W.γD T' W.gam x := by
      rw [← hγE_i, ← hγsm, hEx]
    rw [hdOp, hcomm, smul_sub, hEγ, hEx]
  · intro δ hδ
    rw [hdOp, W.γD_smul, hγE δ hδ, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hΔx δ hδ]
  · split_ifs at hq ⊢ with hk
    · obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) k.toNat
      have hu := rToolMod_unit W ⟨w₁, hw₁⟩ (w₂ : LetA O n) k.toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ k.toNat - 1 := by
        rw [hg]; ring
      have hyΔ : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.NΔ T' :=
        show Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T' ∧ ∀ δ ∈ W.DelF,
            W.γD T' δ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) = Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x from
          ⟨hq, fun δ hδ => by rw [hγsm, map_pow, hΔq δ hδ, hΔx δ hδ]⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x) - Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x =
          W.π₀ • x' := hx'
      have key : Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • Formalism.MainNotions.CrystallineLiftingInputs.dOp W T' x = (↑hu.unit⁻¹ : LetA O n) •
          (x' - ((w₂ : LetA O n) * g) • (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x)) := by
        apply hinj
        rw [hdOp, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat), hcan1,
          smul_comm W.π₀ (↑hu.unit⁻¹ : LetA O n), smul_sub W.π₀, ← hx'', hγy, smul_smul W.π₀, hpg,
          sub_smul, one_smul]
        simp only [smul_sub, smul_smul, ← mul_assoc, hu.val_inv_mul, one_mul]
        abel
      rw [key]
      exact (W.N T').smul_mem _ ((W.N T').sub_mem hx'N ((W.N T').smul_mem _ hq))
    · obtain ⟨y, hyN, rfl⟩ := hq
      obtain ⟨g, hg⟩ := rToolMod_geom (W.π₀ * (w₂ : LetA O n)) (-k).toNat
      have hpg : W.π₀ * ((w₂ : LetA O n) * g) = (1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat - 1 := by
        rw [hg]; ring
      have hyΔ' : ∀ δ ∈ W.DelF, W.γD T' δ y = y := by
        intro δ hδ
        have h1 := hΔx δ hδ
        rw [hγsm, map_pow, hΔq δ hδ] at h1
        rw [← rToolMod_qi_q W T' hqU (-k).toNat (W.γD T' δ y), h1, rToolMod_qi_q W T' hqU]
      have hyΔ : y ∈ W.NΔ T' :=
        show y ∈ W.N T' ∧ ∀ δ ∈ W.DelF, W.γD T' δ y = y from ⟨hyN, hyΔ'⟩
      obtain ⟨x', ⟨hx'N, -⟩, hx'⟩ := hmod2 _ hyΔ
      have hx'' : W.γD T' W.gam y - y = W.π₀ • x' := hx'
      refine ⟨(1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat • x' + ((w₂ : LetA O n) * g) • y,
        (W.N T').add_mem ((W.N T').smul_mem _ hx'N) ((W.N T').smul_mem _ hyN), ?_⟩
      apply hinj
      rw [hdOp, hcan1, hγy, smul_comm W.π₀ (Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat), smul_add W.π₀,
        smul_comm W.π₀ ((1 + W.π₀ * (w₂ : LetA O n)) ^ (-k).toNat), ← hx'', smul_smul W.π₀, hpg,
        sub_smul, one_smul]
      simp only [smul_sub, smul_add, smul_smul, mul_comm]
      abel

end DStab

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_letS (c : ZMod n) (x : W.DD T) : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DelS (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_NcS (c : ZMod n) (x : W.DD T) :
    x ∈ NcS W T c ↔ x ∈ W.N T ∧ (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold NcS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS, mem_letS, and_assoc]

theorem mem_PiNS (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold PiNS
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_DelS]
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN
  rw [Submodule.mem_map]
  rfl

theorem mem_LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ LamPS W T Eπ h' c ↔ Eπ ^ h' • x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) ∧
      (∀ δ ∈ W.DelF, W.γD T δ x = x) ∧ (letE c : LetA O n) • x = x := by
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    mem_DelS, mem_letS, and_assoc]
  rfl

theorem mem_InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) (x : W.DD T) :
    x ∈ InvS W T π' Eπ h' k c ↔ x ∈ LamPS W T Eπ h' c ∧ W.γD T W.gamK x - x ∈ PiNS W T π' k := by
  unfold InvS
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem PiNS_le_N (π' : LetA O n) (k : ℕ) {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ W.N T := by
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := (mem_PiNS W T π' k x).1 hx
  exact (W.N T).smul_mem _ hy

theorem γD_letE (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

theorem φD_letE (c : ZMod n) (x : W.DD T) :
    W.φD T ((letE (c - 1) : LetA O n) • x) = (letE c : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, Formalism.MainNotions.LiftingTheory.wmap_φA_letE]

theorem map_letA_smul {T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x :=
  Formalism.MainNotions.LiftingTheory.wmap_map_smul W f a x

theorem map_comp_zero {T' T'' : LocLat G Qp LL O} (ι : LatHom T.L T'.L) (π : LatHom T'.L T''.L)
    (h0 : ∀ y, π.f (ι.f y) = 0) (x : W.DD T) : W.map π (W.map ι x) = 0 := by
  rw [← W.map_comp]
  have hext : ∀ g₁ g₂ : LatHom T.L T''.L, g₁.f = g₂.f → g₁ = g₂ := by
    rintro ⟨f1, _, _, _⟩ ⟨f2, _, _, _⟩ h
    cases h
    rfl
  have hg : latAdd (latComp π ι) (latComp π ι) = latComp π ι := by
    apply hext
    ext y
    simp [latAdd, latComp, h0]
  have := W.map_latAdd (latComp π ι) (latComp π ι) x
  rw [hg] at this
  exact left_eq_add.mp this

end Local

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Asm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_desc (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {ι : Type} [Fintype ι] (bO : Module.Basis ι O O')
    (bL : Module.Basis ι LL LL') (hb : ∀ i, bL i = algebraMap O' LL' (bO i))
    (hlin : ∀ φ : LL' →ₗ[LL] LL, Continuous φ) [IsLocalRing O'] (hk : lenOl PD (O := O) ≠ ⊤) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') :=
  bcAt_of PD hc hO' hJ (descLift_at PD hc hO' bO bL hb hlin) (descCol_at PD hc hO' bO bL hb hlin hk)

end Asm

end Formalism.MainNotions.UnusedSlot80.BCW
end
end
