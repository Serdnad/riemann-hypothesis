module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013

@[expose] public section

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem γ_smul (a : LetA O n) (x : W.DD T) : W.γ T (a • x) = W.γA W.gam a • W.γ T x :=
  GS.γD_smulA W T W.gam a x

theorem γA_lA (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem φpow_smulA (e : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ e) (a • x) = (W.φA ^ e) a • ((W.φD T) ^ e) x := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, φD_smulA, Module.End.mul_apply]
      <;> rfl

theorem γ_φpow (e : ℕ) (x : W.DD T) : W.γ T (((W.φD T) ^ e) x) = ((W.φD T) ^ e) (W.γ T x) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (W.φγ_comm T W.gam _).symm

theorem γ_Δ {x : W.DD T} (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x := by
  intro δ hδ
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
  rw [← W.γD_mul, mul_comm, W.γD_mul, h δ hδ]

theorem γ_NΔ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {x : W.DD T} (hx : x ∈ W.NΔ T) :
    W.γ T x ∈ W.NΔ T := by
  have hx' : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx
  show W.γ T x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x
  exact ⟨(hP2 T hT).1 W.gam x hx'.1, γ_Δ W hx'.2⟩

theorem γ_NΔi (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨γ_NΔ W hT hP2 h1, ?_⟩
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h2
  refine Submodule.mem_map.2 ⟨W.γ T z, (hP2 T hT).1 W.gam z hz, ?_⟩
  rw [← hzx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [γ_smul, GS.γA_letE]

theorem γ_Pp (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {y : W.DD T}
    (hy : y ∈ Pp W T c e) : W.γ T y ∈ Pp W T c e := by
  have key : Pp W T c e ≤ (Pp W T c e).comap (W.γ T).toAddMonoidHom := by
    unfold Pp
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.mem_comap.2 ?_
    show W.γ T (a • ((W.φD T) ^ e) x) ∈ _
    rw [γ_smul, γ_φpow]
    exact AddSubgroup.subset_closure ⟨_, GS.γA_mem W W.gam ha, _, γ_NΔi W hT hP2 hx, rfl⟩
  exact key hy

theorem γ_InFP (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {f : LetA O n}
    {x : W.DD T} (h : InFP W T c e f x) : InFP W T c e (W.γA W.gam f) (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨W.γ T y, γ_Pp W hT hP2 hy, γ_smul W f y⟩

theorem inMultiple_zero {c : ZMod n} {e : ℕ} {f : LetA O n} : InFP W T c e f 0 :=
  ⟨0, (Pp W T c e).zero_mem, (smul_zero f).symm⟩

theorem inMultiple_sum {c : ZMod n} {e : ℕ} {f : LetA O n} {ι : Type} (s : Finset ι) (x : ι → W.DD T)
    (h : ∀ i ∈ s, InFP W T c e f (x i)) : InFP W T c e f (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact inMultiple_zero W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨y, hy, hxy⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨y', hy', hxy'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨y + y', (Pp W T c e).add_mem hy hy', by rw [hxy, hxy', smul_add]⟩

theorem InI_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T}
    (h : InI W T c w) : InI W T c (W.γ T w) := by
  obtain ⟨h1, h2, ⟨y, hy, hyc, hxy⟩⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  obtain ⟨u, hu, hγπ⟩ := hpi0
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • W.γ T w = W.γ T w
    rw [← GS.γA_letE W W.gam c, ← γ_smul, h1]
  · exact γ_Δ W h2
  · refine ⟨u • W.γ T y, TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy), ?_, ?_⟩
    · rw [smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · have : W.γ T (W.γ T w) - W.γ T w = W.γ T (W.γ T w - w) := by rw [map_sub]
      rw [this, hxy, γ_smul, hγπ, mul_smul]

theorem InI_smulA {c : ZMod n} {a : LetA O n} (ha : a ∈ W.AΔ) (ha' : W.γA W.gam a = a) {w : W.DD T}
    (h : InI W T c w) : InI W T c (a • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (a • w) = a • w
    rw [smul_comm, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (a • w) = a • w
    intro δ hδ
    rw [GS.γD_smulA, ha δ hδ, h2 δ hδ]
  · have : W.γ T (a • w) - a • w = a • (W.γ T w - w) := by rw [γ_smul, ha', smul_sub]
    rw [this]
    exact TypesA.InFNc_smul W ha h3

theorem InI_smulO {c : ZMod n} (o : O) {w : W.DD T} (h : InI W T c w) : InI W T c (o • w) := by
  obtain ⟨h1, h2, y, hy, hyl, hyx⟩ := h
  refine ⟨?_, ?_, o • y, (W.NΔ T).smul_mem o hy, ?_, ?_⟩
  · unfold InLet at h1 ⊢
    rw [smul_comm, h1]
  · intro δ hδ
    rw [map_smul, h2 δ hδ]
  · rw [smul_comm, hyl]
  · rw [map_smul, ← smul_sub, hyx, smul_comm]

theorem InI_sum {c : ZMod n} {ι : Type} (s : Finset ι) (x : ι → W.DD T) (h : ∀ i ∈ s, InI W T c (x i)) :
    InI W T c (∑ i ∈ s, x i) := by
  classical
  have hadd : ∀ x y, InI W T c x → InI W T c y → InI W T c (x + y) := by
    rintro x y ⟨hx1, hx2, u, hu, hul, hux⟩ ⟨hy1, hy2, u', hu', hul', hux'⟩
    refine ⟨?_, ?_, u + u', (W.NΔ T).add_mem hu hu', ?_, ?_⟩
    · unfold InLet at hx1 hy1 ⊢
      rw [smul_add, hx1, hy1]
    · intro δ hδ
      rw [map_add (f := _), hx2 δ hδ, hy2 δ hδ]
    · rw [smul_add, hul, hul']
    · rw [map_add (f := _), add_sub_add_comm, hux, hux', smul_add]
  have hzero : InI W T c 0 := ⟨by unfold InLet; rw [smul_zero], fun δ _ => map_zero _, 0,
    (W.NΔ T).zero_mem, smul_zero _, by rw [map_zero, sub_zero, smul_zero]⟩
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hzero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem InI_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w) (i : ℕ) :
    InI W T c ((W.γ T)^[i] w) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InI_γ W hT hP2 hpi0 ih

theorem aeval_eq (P : Polynomial O) (x : W.DD T) :
    Polynomial.aeval (W.γ T) P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γ T)^[i] x := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem aevalE_eq (P : Polynomial O) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γE W.gam)^[i] f := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem InI_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w)
    (P : Polynomial O) : InI W T c (Polynomial.aeval (W.γ T) P w) := by
  rw [aeval_eq]
  exact InI_sum W _ _ fun i _ => InI_smulO W _ (InI_iter W hT hP2 hpi0 h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

theorem phi_smul (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  show W.φD T (a • x) = (letφ W.φ₀ a) • W.φD T x
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

variable {W} [IsDomain O] [FiniteDimensional Qp LL]

theorem π₀_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : W.π₀ j ≠ 0 := by
  obtain ⟨w, hw⟩ := hR.1
  intro h0
  have h1 : W.π₀ j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) := by
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1] at h0
  have hu : IsUnit ((w : LetA O n) j) := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) j)
  have hX : (PowerSeries.X : PowerSeries O) ^ (PD.p - 1) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  exact hX (hu.mul_right_eq_zero.mp h0)

theorem cancel_π₀ (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {x y : LetA O n} (h : W.π₀ * x = W.π₀ * y) : x = y := by
  funext j
  have h' := congrFun h j
  simp only [Pi.mul_apply] at h'
  exact mul_left_cancel₀ (π₀_letter_ne hR j) h'

theorem qA_letter_cc (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : constantCoeff (qA W j) = ((PD.p : ℕ) : O) := by
  obtain ⟨w, hw⟩ := hR.1
  have hp2 : 2 ≤ PD.p := PD.hp.two_le
  have h1 : qA W j = (w : LetA O n) j * PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) := by
    show W.π₀ j + (lA W) j = _
    rw [hw, Pi.mul_apply, Pi.pow_apply]
    rfl
  rw [h1, map_add (f := _), map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero, zero_add,
    map_natCast]

theorem qA_letter_ne (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) (j : ZMod n) : qA W j ≠ 0 := by
  intro h
  have hc := qA_letter_cc hR j
  rw [h, map_zero] at hc
  have hv := W.v_l
  have h0 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), ← hc, map_zero]
  rw [h0, AddValuation.map_zero] at hv
  simp at hv

theorem w_mem (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) :
    ∃ w ∈ W.AΔ, IsUnit w ∧ W.φA W.π₀ = w * W.π₀ * qA W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.1
  have hinv : ∀ g, g ∈ W.DelF → g⁻¹ ∈ W.DelF := by
    intro g hg
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def g).1 hg
    exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hk', inv_one]⟩
  have hmul : ∀ a b, a ∈ W.DelF → b ∈ W.DelF → a * b ∈ W.DelF := by
    intro a b ha hb
    obtain ⟨k, hk, hk'⟩ := (W.DelF_def a).1 ha
    obtain ⟨m, hm, hm'⟩ := (W.DelF_def b).1 hb
    refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [mul_pow, pow_mul, hk', one_pow, one_mul, mul_comm k m, pow_mul, hm', one_pow]
  have hπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := by
    intro δ hδ
    funext i
    show W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold Formalism.BasicNotions.LocWach.π₀₁

    rw [map_add (f := _), map_sub, map_one, map_natCast, map_sum]
    congr 1
    have hsum : ∀ x ∈ W.DelF, W.γ₀ δ (W.γ₀ x (1 + PowerSeries.X)) = W.γ₀ (δ * x) (1 + PowerSeries.X) := by
      intro x _
      rw [map_mul, AlgHom.mul_apply]
    rw [Finset.sum_congr rfl hsum]
    refine Finset.sum_equiv (Equiv.mulLeft δ) (fun g => ?_) (fun g _ => rfl)
    constructor
    · intro hg
      exact hmul δ g hδ hg
    · intro hg
      have := hmul δ⁻¹ (δ * g) (hinv δ hδ) hg
      rwa [inv_mul_cancel_left] at this
  have hq : ∀ δ ∈ W.DelF, W.γA δ (qA W) = qA W := by
    intro δ hδ
    show W.γA δ (W.π₀ + lA W) = W.π₀ + lA W
    rw [map_add (f := _), hπ δ hδ]
    congr 1
    show W.γA δ ((PD.p : ℕ) : LetA O n) = ((PD.p : ℕ) : LetA O n)
    exact map_natCast _ _
  have hc : ∀ δ (a : LetA O n), W.γA δ (W.φA a) = W.φA (W.γA δ a) := by
    intro δ a
    funext i
    show W.γ₀ δ (W.φ₀ (a (i - 1))) = W.φ₀ (W.γ₀ δ (a (i - 1)))
    rw [W.γ₀_comm]
  refine ⟨w, ?_, w.isUnit, hw⟩
  show ∀ δ ∈ W.DelF, W.γA δ (w : LetA O n) = w
  intro δ hδ
  have e1 := congrArg (W.γA δ) hw
  rw [hc, hπ δ hδ, map_mul, map_mul, map_pow, hπ δ hδ, hq δ hδ, hw] at e1
  funext j
  have e2 := congrFun e1 j
  simp only [Pi.mul_apply, Pi.pow_apply] at e2
  have hne : W.π₀ j * qA W j ^ (PD.p - 1) ≠ 0 :=
    mul_ne_zero (π₀_letter_ne hR j) (pow_ne_zero _ (qA_letter_ne hR j))
  apply mul_left_cancel₀ hne
  linear_combination -e2

theorem coord_mod (hR : Formalism.MainNotions.N.FrobeniusPowerSeries.GS.RD W) {T : LocLat G Qp LL O} {i : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    ∃ (c₀ : Fin d → O) (z : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T i z ∧
      x = Formalism.MainNotions.LiftingTheory.vecB W T b c₀ + W.π₀ • z := by
  obtain ⟨a, ⟨haA, hxa⟩, -⟩ := hb.2 x hx
  choose F hF using fun m => hR.2.2.2 (a m) (haA m).1
  have hs : HasSubst W.π₀₁ := HasSubst.of_constantCoeff_zero' (Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀₁_cc hR)
  let c₀ : Fin d → O := fun m => constantCoeff (F m i)
  let g : Fin d → PowerSeries O := fun m => substAlgHom hs (mk fun k => coeff (k + 1) (F m i))
  let a' : Fin d → LetA O n := fun m => Pi.single i (g m)
  have hzero : ∀ m, ∀ j, j ≠ i → a m j = 0 := by
    intro m j hj
    have := congrFun (haA m).2 j
    simp only [Pi.mul_apply, letE, Pi.single_apply, hj, if_false, zero_mul] at this
    exact this.symm
  have key : ∀ m, a m = algebraMap O (LetA O n) (c₀ m) * letE i + W.π₀ * a' m := by
    intro m
    funext j
    by_cases hj : j = i
    · subst hj
      have e1 : a m j = substAlgHom hs (F m j) := by rw [hF m j, coe_substAlgHom]; rfl
      rw [e1]
      conv_lhs => rw [eq_shift_mul_X_add_const (F m j)]
      rw [map_add (f := _), map_mul, substAlgHom_X hs]
      have e2 : substAlgHom hs (C (constantCoeff (F m j))) = C (constantCoeff (F m j)) := by
        rw [coe_substAlgHom, subst_C]
        rfl
      rw [e2]
      show _ = (algebraMap O (LetA O n) (c₀ m)) j * (letE (O := O) j : LetA O n) j + W.π₀ j * a' m j
      have e3 : (algebraMap O (LetA O n) (c₀ m)) j = C (c₀ m) := rfl
      simp only [e3, letE, a', g, c₀, Pi.single_eq_same, mul_one]
      show _ = C (constantCoeff (F m j)) + W.π₀₁ * _
      ring
    · simp only [Pi.add_apply, Pi.mul_apply, letE, Pi.single_apply, hj, if_false, mul_zero, a', zero_add, hzero m j hj]
  have h1 : ∀ m, W.π₀ * a' m = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
    intro m
    rw [key m]
    ring
  refine ⟨c₀, ∑ m, a' m • b m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1
  · intro δ hδ

    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γD_smulA, (hb.1 m).1.2 δ hδ]
    congr 1
    apply cancel_π₀ hR
    calc W.π₀ * W.γA δ (a' m) = W.γA δ (W.π₀ * a' m) := by
          rw [map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W δ hδ]
      _ = W.γA δ (a m - algebraMap O (LetA O n) (c₀ m) * letE i) := by rw [h1]
      _ = a m - algebraMap O (LetA O n) (c₀ m) * letE i := by
          rw [map_sub, map_mul, (haA m).1 δ hδ, AlgHom.commutes, Formalism.MainNotions.N.FrobeniusPowerSeries.GS.γA_letE]
      _ = W.π₀ * a' m := (h1 m).symm
  · refine ⟨∑ m, a' m • b m, Submodule.sum_mem _ fun m _ => (W.N T).smul_mem _ (hb.1 m).1.1, ?_⟩
    show (letE i : LetA O n) • (∑ m, a' m • b m) = ∑ m, a' m • b m
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [letE, a']
    · simp [letE, a', hj]
  · rw [hxa]
    simp only [Formalism.MainNotions.LiftingTheory.vecB]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hlet : (letE i : LetA O n) • b m = b m := Formalism.MainNotions.N.FrobeniusPowerSeries.TypesD.nl_letter W (hb.1 m).2
    rw [key m, add_smul, mul_smul, hlet, algebraMap_smul, mul_smul]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAa
end
end
