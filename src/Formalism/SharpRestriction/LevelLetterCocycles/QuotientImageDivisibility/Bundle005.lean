module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section GenM

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {LL : Type} [Field LL]
  [Algebra O LL] [IsFractionRing O LL] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  {U : Type} [AddCommGroup U] [Module LL U]

theorem genM (φ : M →+ U) (hφ : ∀ (c : O) (x : M), φ (c • x) = algebraMap O LL c • φ x) {m : ℕ}
    (hm : Module.finrank LL ↥(Submodule.span LL (Set.range φ)) ≤ m) :
    ∃ s : Finset M, s.card ≤ m ∧ ∀ x : M, ∃ y ∈ Submodule.span O (↑s : Set M), φ (x - y) = 0 := by
  let A : Submodule O M := ⊤
  let φ' : ↥A →+ U := φ.comp A.subtype.toAddMonoidHom
  have hφ' : ∀ (c : O) (x : ↥A), φ' (c • x) = algebraMap O LL c • φ' x := fun c x => hφ c x
  have hr : Set.range φ' = Set.range φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨x, trivial⟩, rfl⟩
  have hm' : Module.finrank LL ↥(Submodule.span LL (Set.range φ')) ≤ m := by rwa [hr]
  obtain ⟨-, Q, i1, i2, ob, hker, hgen, -⟩ :=
    pstep_rank (lenO := 0) (m := m) (c := 0) A φ' hφ' hm'
  obtain ⟨sQ, hsQ, hspan⟩ := hgen trivial
  obtain ⟨t, ht, htN, hNt⟩ := Formalism.MainNotions.RamifiedCoefficientChains.exists_gen_of_le_span sQ (LinearMap.range ob)
    (by rw [hspan]; exact le_top)
  have hpre : ∀ q : ↥t, ∃ x : ↥A, ob x = q := fun q => htN q.2
  choose f hf using hpre
  refine ⟨Finset.univ.image (fun q : ↥t => ((f q : ↥A) : M)), ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_coe]
    exact ht.trans hsQ
  · have hx : ob ⟨x, trivial⟩ ∈ Submodule.span O (↑t : Set Q) := hNt ⟨_, rfl⟩
    rw [Submodule.mem_span_finset] at hx
    obtain ⟨a, -, hax⟩ := hx
    set y : M := ∑ q : ↥t, a q • ((f q : ↥A) : M) with hy
    refine ⟨y, Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ q)))), ?_⟩
    have hoby : ob ⟨y, trivial⟩ = ob ⟨x, trivial⟩ := by
      have e : (⟨y, trivial⟩ : ↥A) = ∑ q : ↥t, a q • f q := Subtype.ext (by simp [hy])

      rw [e, map_sum, ← hax]
      rw [← Finset.sum_coe_sort t]
      exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hf q]
    have h0 : ob (⟨x, trivial⟩ - ⟨y, trivial⟩) = 0 := by rw [map_sub, hoby, sub_self]
    have hz := (hker _).1 h0
    have := (mem_zeroSub_coe A φ' hφ' (⟨x, trivial⟩ - ⟨y, trivial⟩)).1 hz
    simpa [φ'] using this

end GenM

section Frame

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem NDl_coords (i : ZMod n) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    ∃ (d : ℕ) (b : Fin d → W.DD T), (∀ k, b k ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ∧
      ∀ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i, ∃ α : Fin d → O,
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T y = ∑ k, algebraMap O LL (α k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) := by
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T i hmod
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE i : LetA O n) • b k = b k := fun k =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T i (hb.1 k).2
  refine ⟨d, b, fun k => ⟨hbN k, hbl k, (hb.1 k).1.2⟩, fun y hy => ?_⟩
  have hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y := hy
  have hyi : Formalism.MainNotions.LiftingTheory.InNΔi W T i y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T i ⟨hy'.1, hy'.2.2⟩ hy'.2.1
  obtain ⟨a, ⟨-, hya⟩, -⟩ := hb.2 y hyi
  refine ⟨fun k => PowerSeries.constantCoeff ((a k) i), ?_⟩
  rw [hya, cmpD_sum W T _ _ (fun k _ => (W.N T).smul_mem _ (hbN k))]
  exact Finset.sum_congr rfl fun k _ => cmpD_smul_letter W T i (a k) (hbN k) (hbl k)

end Frame

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem exists_X_pow_mul (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (w : ℕ) (u : PowerSeries LL), PowerSeries.constantCoeff u ≠ 0 ∧ f = PowerSeries.X ^ w * u := by
  have hex : ∃ w, PowerSeries.coeff w f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (PowerSeries.ext fun w => by simpa using h w)
  obtain ⟨w, h1, hmin⟩ : ∃ w, PowerSeries.coeff w f ≠ 0 ∧ ∀ m < w, PowerSeries.coeff m f = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      push Not at this
      exact this⟩
  have hdvd : PowerSeries.X ^ w ∣ f := PowerSeries.X_pow_dvd_iff.2 hmin
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨w, u, ?_, hu⟩
  rw [hu, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
  exact h1

theorem smulS_div {m : ℤ} {e : ℤ → V} (he : LB m e) (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_inj {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (f : PowerSeries LL)
    (hf : f ≠ 0) (h : smulS f d = smulS f d') : d = d' := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  have h0 : smulS (PowerSeries.X ^ w * u) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS u (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + w)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') u hu
  rw [h1] at h2
  have h3 : smulS u⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

theorem smulS_comm {m : ℤ} {d : ℤ → V} (hd : LB m d) (f g : PowerSeries LL) :
    smulS f (smulS g d) = smulS g (smulS f d) := by
  rw [← smulS_mul hd, ← smulS_mul hd, mul_comm]

theorem smulS_mem {m : ℤ} {d : ℤ → V} (hd : LB m d) (D : Submodule LL V) (hD : ∀ k, d k ∈ D)
    (f : PowerSeries LL) (k : ℤ) : smulS f d k ∈ D := by
  have := Dg_smulS (Fil := fun _ : ℤ => D) (fun _ _ _ => le_rfl) hd (s := 0)
    (fun k => hD k) f k
  simpa using this

end Div

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem conv_eq {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv f d = smulS f d := rfl

theorem p_ne_zero_LL (W' : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h
  have := W'.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem eat_qp :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]

theorem expRing_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := by
  intro hA i ζ hζ
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨u₀, hu₀, hq⟩ := MC.lev_q_eq W i hζ hp
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_qp] at hw

  have hqp : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) =
      (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) * PowerSeries.X := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hq]
    ring
  have hunit : IsUnit (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) :=
    ((Units.isUnit _).map _).mul
      (PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hu₀))
  have hcq : PowerSeries.constantCoeff (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W)) = 0 := by
    rw [hqp, map_mul, PowerSeries.constantCoeff_X, mul_zero]
  have hcpi : PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
    rw [e, map_add (f := _), map_natCast, map_add (f := _), map_natCast] at hcq
    linear_combination hcq
  refine ⟨⟨_, hunit, hqp⟩, hcpi, ?_⟩

  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.1
  rw [eat_qp] at hw'
  have hp1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hcφ : PowerSeries.constantCoeff (W.lev i ζ (W.φA W.π₀)) = 0 := by
    rw [hw', map_mul, map_mul, map_pow, map_mul, map_mul, map_pow, hcq,
      zero_pow (by omega), mul_zero]
  have e2 : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA W.π₀ + ((PD.p : ℕ) : LetA O n) := by
    simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, map_natCast]
  rw [e2, PowerSeries.isUnit_iff_constantCoeff, map_add (f := _), map_natCast, map_add (f := _), hcφ, zero_add,
    map_natCast]
  exact isUnit_iff_ne_zero.2 hp

def GamN : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : ↥(W.N T)) (hx : W.γ T (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γ T x, hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T i ζ x k

def GamA : Prop :=
  ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
    W.lev i ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ f)

theorem gam_of_tie (hs : W.s = 1) {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamN W ∧ GamA W := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    simp only [Nat.cast_one]
    rw [W.gam_gen, hs, Nat.cast_one]
  refine ⟨fun T hT i ζ hζ x hx k => ?_, fun i ζ hζ f => ?_⟩
  · rw [C.levN_eq, C.levN_eq]
    have e := C.levB_Γ T hT W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) x hx k
    have e' : (⟨W.γ T x, hx⟩ : ↥(W.N T)) = ⟨W.γD T W.gam x, hx⟩ := rfl
    rw [e', e, map_smul]
  · exact C.lev_Γ W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) f

end Exp

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
