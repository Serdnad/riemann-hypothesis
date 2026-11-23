module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle036
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle035
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle029
import Formalism.SharpRestriction.LevelLetterCocycles.HorTrUnique
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle032
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle034
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle037
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle019
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def SecCrit0 (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    (InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x ↔
      ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
        (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m)

theorem inFNc_smul (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (a : ZMod n) {c : LetA O n} (hc : c ∈ W.AΔ)
    {x : W.DD T} (hx : InFNc W T a 1 x) : InFNc W T a 1 (c • x) := by
  obtain ⟨y, hy, hyl, rfl⟩ := hx
  exact ⟨c • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hc hy, by rw [smul_comm, hyl], by simp⟩

theorem inFP_up (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n)
    (e N : ℕ) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • y)) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T y)) := by
  obtain ⟨p, hp, hyp⟩ := hy
  rw [one_smul] at hyp
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  refine ⟨(ps W 0 ^ N * vv * ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) • W.φD T p,
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv)
      (W.AΔ.pow_mem hp0Δ _)) _ (φ_Pp W T c' e p hp), ?_⟩
  rw [one_smul, lam_succ, ← hyp, φD_smulA, smul_smul, smul_smul]
  unfold LamUp
  congr 1; ring

theorem good_zero (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) : Good A c' e T b sol 0 := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (0 : W.DD T)) := by
    rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hT.1 c' b sol hb (A.M PD.p)
  refine good_of_sec C A hA c' hc' T hT b sol hb e 0 hz 0 (fun _ => 0)
    ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
      simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩
    (fun m => inFr_zero W) 0 ?_
  simpa using secIn_zero W (condNN W T (c' + (e : ZMod n)) e b) (a := c' + (e : ZMod n)) (e := e)

theorem good_sum (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, Good A c' e T b sol (z j)) : Good A c' e T b sol (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_zero C A hA c' hc' T hT b sol hb e
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact good_add C A hA c' hc' T hT b sol hb e _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem φE_lE (t : ℕ) : W.φE (lE W t) = lE W t := by
  unfold lE; rw [map_pow, map_natCast]

theorem step_mp (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hxN : InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x) : Good A c' (e + 1) T b sol x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set hq : ℕ := Hw A.G₀ A.S A.η (A.ty (a + 1)) with hqdef
  set U : LetA O n := LamUp W A c' e with hUdef
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ (H + hq))
      (cop_lamUp W C.hR C.hp0 A c' e (H + hq))

  have g0 : Good A c' (e + 1) T b sol (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' (e + 1) T hT.1
      b sol hb x hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * U) (ps W 0 ^ H)
        (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    obtain ⟨κ₀, hS⟩ := (h0 (u₀ • x) κ _ hz hrep0 hfr0).1 (inFNc_smul C.hR.1 T _ hu₀ hxN)
    exact good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ hz κ _ hrep0 (fun m => inFr_mulA W (hfr m) hu₀) κ₀ hS

  obtain ⟨r, bb, β, hbb, hβ, hdec⟩ := exists_smul_pow_eq_sum_of_inFNc C T A hA hT a hq le_rfl x (by rwa [ha'] at hxN)
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have gj : ∀ j, Good A c' (e + 1) T b sol ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
    intro j
    have hbl : (letE a : LetA O n) • bb j = bb j := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T a (hbb j).2
    have hbN : InFNc W T a 1 (bb j) := ⟨bb j, (hbb j).1, hbl, (one_smul _ _).symm⟩
    have hbP : InFP W T c' e 1 (abelian₂ W A a e • bb j) :=
      Formalism.MainNotions.UnusedSlot80.ArcC.arc_down W C.hs C.hR T A hA h5T (C.hmod T hT.1) C.hΔ c' hc' e (bb j) hbN
    obtain ⟨κj, fj, hrepj, hfrj⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1
      b sol hb (bb j) hbP
    obtain ⟨κ'j, hSj⟩ := (IH (bb j) κj fj hbP hrepj hfrj).1 hbN
    have hv : s₁ * β j ∈ W.AΔ := W.AΔ.mul_mem hs₁ (hβ j)
    have hPκ : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (lA W ^ κj • bb j)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κj) hbP
    obtain ⟨-, hrep', -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
      (by simpa using hrepj) hfrj H le_rfl hv
    have hel : (ps W 0 ^ H * (s₁ * β j)) • W.φD T (lA W ^ κj • bb j) =
        lA W ^ κj • ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
      rw [φD_smulA, φA_lA, smul_comm]
    rw [hel] at hrep'
    have hlow0 : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ)) := by
      intro c₀
      have := dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 (e + 1) 0 (by omega) c₀
      rw [hHdef, ha']; rwa [ha'] at this
    have hS' := secIn_transport W T a e b H hv C.hR.1 hlow0 _ hSj
    rw [← ha'] at hS'
    refine good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ (inFP_up C.hR T A c' e H hv (bb j) hbP) κj _ hrep'
      (fun m => (transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
        (by simpa using hrepj) hfrj H le_rfl hv).2.2 m) κ'j ?_
    convert hS' using 1
    funext m
    rw [map_mul W.φE, φE_lE]
    ring
  have hu₁x : u₁ • x = ∑ j, (ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j) := by
    rw [hu₁e, show ps W 0 ^ (H + hq) * s₁ = (ps W 0 ^ H * s₁) * ps W 0 ^ hq by ring, mul_smul, hdec,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; congr 1; ring
  have g1 : Good A c' (e + 1) T b sol (u₁ • x) := by
    rw [hu₁x]
    exact good_sum C A hA c' hc' T hT b sol hb (e + 1) _ _ fun j _ => gj j
  have g2 : Good A c' (e + 1) T b sol (lA W ^ m₀ • x) := by
    rw [hl, add_smul]
    exact good_add C A hA c' hc' T hT b sol hb (e + 1) _ _ g0 g1
  exact good_of_lpow C A hA c' hc' T hT b sol hb (e + 1) m₀ x hxP g2

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem sigma_bound_le (l h η : ℕ) (hl : 11 ≤ l) :
    ((2 * S9.sigC l h η : ℕ) : ℝ) ≤ S9.ExtensionLemmaAlt.B2 l h η := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hx : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) + 1 := by
    have : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hc := Nat.ceil_lt_add_one hx
  unfold S9.ExtensionLemmaAlt.B2 Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig
  unfold S9.sigC
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  push_cast
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar at hc
  push_cast at hc
  linarith

theorem eta_le_parameter (l h η : ℕ) (hl : 2 ≤ l) (hη : η ≤ h) : η ≤ (l - 1) * Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  have := Nat.lt_mul_div_succ h (by omega : 0 < l - 1)
  omega

theorem jumps_bounds_of_set [NeZero n] (W : LocWach PD LL O v n) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) (hS : SetCS W d T₁ T₂ F b S η m) :
    (∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T₂.ρ τ (Set.Ici (-((hpar n b S : ℕ) : ℤ)))) ∧
    ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) := by
  have hn : Even n := hS.2.2.1
  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i → -((hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  exact ⟨fun i τ hτ a ha => hwin i a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS i τ hτ a ha),
    fun c' τ hc' hτ a ha => hwinU c' hc' a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS (c' + 1) τ hτ a ha)⟩

theorem difference_of_factorisations {M' : Type} [AddCommGroup M'] [Module O M'] {R : Type} [CommRing R] [Module R M']
    [SMulCommClass O R M'] (f0 : R) (l : O) (φw tw t₁ t' t p₁ p₂ p₃ : M')
    (etw : tw - ((1 : O) • t₁ + (-l) • t') = f0 • p₁) (e₂ : t₁ = f0 • p₂) (e₃ : t - t' = f0 • p₃) :
    (l • φw - tw) - l • (φw + t) = f0 • (-(p₁ + p₂ + l • p₃)) := by
  have et' : t' = t - f0 • p₃ := by rw [← e₃]; abel
  have etw' : tw = f0 • p₁ + ((1 : O) • t₁ + (-l) • t') := by rw [← etw]; abel
  rw [etw', e₂, et']
  simp only [one_smul, neg_smul, smul_sub, smul_add, smul_neg]
  rw [smul_comm l f0 p₃]
  abel

theorem pow_smul_cocycle_sub_sum_mem_latticeCoboundaries (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (ev : Finset (ZMod n))
    (xc : ZMod n → ↥(W.wachCocyclesDelta T)) (κ : ZMod n → G → T.V) (hκ : ∀ c, κ c ∈ latticeCocycles T.L)
    (hP : ∀ c ∈ ev, W.clK T (xc c) = Submodule.Quotient.mk ⟨κ c, hκ c⟩)
    (x0 : ↥(W.wachCocyclesDelta T)) (gf : G → T.V) (hgf : gf ∈ latticeCocycles T.L)
    (hcl0 : W.clK T x0 = Submodule.Quotient.mk ⟨gf, hgf⟩) (e : ℕ)
    (hcls : ∑ c ∈ ev, W.clK T (xc c) = ((PD.p : ℕ) : O) ^ e • W.clK T x0) :
    (PD.p : O) ^ e • gf - ∑ c ∈ ev, κ c ∈ latticeCoboundaries T.L := by
  let Ks : ↥(latticeCocycles T.L) := ∑ c ∈ ev, ⟨κ c, hκ c⟩
  have hK : (Submodule.Quotient.mk Ks : LatticeCohomology T.L) = ∑ c ∈ ev, W.clK T (xc c) := by
    calc (Submodule.Quotient.mk Ks : LatticeCohomology T.L)
        = ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ Ks := rfl
      _ = ∑ c ∈ ev, ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ ⟨κ c, hκ c⟩ := map_sum _ _ _
      _ = ∑ c ∈ ev, W.clK T (xc c) := Finset.sum_congr rfl fun c hc => (hP c hc).symm
  have hgf0 : (Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ e • (⟨gf, hgf⟩ : ↥(latticeCocycles T.L)) - Ks) :
      LatticeCohomology T.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hK, hcls, hcl0, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hgf0
  rw [Submodule.mem_comap] at hmem
  simpa [Ks, Submodule.coe_sum] using hmem

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letterIdempotentMap (i : ZMod n) : W.DD T →ₗ[O] W.DD T where
  toFun x := (letE i : LetA O n) • x
  map_add' x y := smul_add _ x y
  map_smul' r x := Formalism.MainNotions.N.Pv.LocalLengthBound.osmul_comm W T (letE i) r x

variable {W T}

theorem frobenius_lift_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1) =
      ((PD.p : ℕ) : O) ^ σ • W.φD T (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • yv) +
          W.φD T (μ c) - μ (c + 1)) - ((PD.p : ℕ) : O) ^ N • t c := by
  unfold liftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem gamma_difference_identity (N s₁ σ : ℕ) (yv zv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    W.γ T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) -
      (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) =
      ((PD.p : ℕ) : O) ^ N • gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • zv) +
          (W.γ T (μ (c + 1)) - μ (c + 1))) := by
  unfold gammaDefectOfLiftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem frobenius_difference_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t (c - 2) -
          ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c - 1)) -
        ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE c : LetA O n) • yv) +
          W.φD T (μ (c - 1)) - μ c) := by
  unfold frobeniusShiftDefectOfLiftCorrection
  simp only [map_sub, map_add (f := _), map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

end Fam

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

end
end
