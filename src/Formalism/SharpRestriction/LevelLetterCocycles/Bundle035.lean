module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle034
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle033
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfFrame

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

theorem tau_over (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

theorem dvO_letter (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

variable [IsDomain O]

theorem dvO_filLow (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s (-(A.Hs (c' + (e : ZMod n)) e s : ℤ)) := by
  set i : ZMod n := c' + ((e - s : ℕ) : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → -(A.Hs (c' + (e : ZMod n)) e s : ℤ) ≤ a := by
    intro a ha
    have hw := Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)
    have hle := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' e (e - s) (by omega) (by omega)
    rw [show e - (e - s) = s by omega, ← hidef] at hle
    have := hw.1
    push_cast at this ⊢
    omega
  have hy := fil_low W T i τ hover hbij.2 _ hJ (dvO_letter W T c' b hb (e - s) c₀)
  refine ⟨dvO W T (e - s) b c₀, ⟨hy, ?_⟩, ?_⟩
  · rw [show c' + (e : ZMod n) - (s : ZMod n) = i by rw [hidef]; push_cast [Nat.cast_sub hse.le]; ring]
    exact dvO_letter W T c' b hb (e - s) c₀
  · rw [← dvO_add, Nat.sub_add_cancel hse.le]

theorem dvO_zero_high [NeZero n] (hbij : Function.Bijective (algebraMap K₀ K))
    (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (u : ℤ)
    (hu : (A.Hs (c' + (e : ZMod n)) e s : ℤ) < u) (c₀ : Fin d → O)
    (h : dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hHw : Hw A.G₀ A.S A.η (A.ty i) ≤ A.Hs (c' + (e : ZMod n)) e s :=
    Formalism.MainNotions.UnusedSlot80.ArcC.hw_le_hs A hA c' hc' e s hse
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun a ha =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)).2
  have hy0 := fil_high W T i τ hover hbij.2 _ hJ u (by omega) hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem secIn_piLam (hπ : W.π₀ ∈ W.AΔ) (A : ArcP n) (a : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T)
    (hlow : ∀ c₀ : Fin d → O, ∀ s < e, dvO W T e b c₀ ∈ FilS W T a s (-(A.Hs a e s : ℤ)))
    (h : Fin d → W.EE) (hh : ∀ k, InFr W a (W.π₀ * abelian₂ W A a e) 1 (h k)) :
    SecIn W a e (condNN W T a e b) h := by
  refine ⟨d, h, fun i => Pi.single i 1, fun _ s => (A.Hs a e s : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hhu⟩ := hh i
    refine ⟨W.π₀ * u, W.AΔ.mul_mem hπ hu, ?_⟩
    have hnum : ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat = abelian₂ W A a e := by
      simp [abelian₂]
    have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 :=
      Finset.prod_eq_one fun s _ => by rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat) * h i =
      algebraMap (LetA O n) W.EE ((letE a * ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat) *
        (W.π₀ * u))
    rw [hden, hnum, ← one_mul (h i), ← map_one (algebraMap (LetA O n) W.EE), hhu, map_one, one_mul]
    congr 1; ring
  · intro s hs; exact hlow _ s hs
  · simp [Pi.single_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevEv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  hp : ((PD.p : ℕ) : F) ≠ 0
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ ζ (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ, ev ζ (letE a) = 1
  ev_ps : ∀ ζ, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g ζ x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤
  div : ∀ g ∈ W.AΔ, (∀ ζ, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w
  rat : ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ, ev ζ d ≠ 0) → ∀ c : F, (∀ ζ, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

attribute [instance] LevEv.fF LevEv.algOF

theorem invLevCore_of (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hL : ∀ a s, LevEv W a s)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W := by
  intro _hA _hp a s T e hsT f hf hγ
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨κ, v, hv, hfv⟩ := hγ
  let L := hL a s
  letI : Field L.F := L.fF
  letI : Algebra O L.F := L.algOF
  set D : LetA O n := ∏ t ∈ T, ps W t ^ e t with hDdef
  set U : LetA O n := letE a * 1 * u with hUdef
  have hDΔ : D ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (RatW.ps_mem W hπ t) _
  have hUΔ : U ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (W.AΔ.one_mem)) hu
  have hUe : letE a * U = U := by rw [hUdef, ← mul_assoc, ← mul_assoc, RatW.letE_idem]

  have hp0 : ((PD.p : ℕ) : L.F) ≠ 0 := L.hp
  have hγE' : algebraMap (LetA O n) W.EE (W.γA W.gam D) * W.γE W.gam f =
      algebraMap (LetA O n) W.EE (W.γA W.gam U) := by
    have h1 : W.γE W.gam (algebraMap (LetA O n) W.EE D * f) = W.γE W.gam (algebraMap (LetA O n) W.EE U) := by
      rw [hfu]
    rw [map_mul, W.γE_ext, W.γE_ext] at h1
    exact h1
  have hA : ((PD.p : ℕ) : LetA O n) ^ κ * (D * W.γA W.gam U - W.γA W.gam D * U) =
      W.γA W.gam D * (letE a * ps W s * v) := by
    apply W.EE_inj
    simp only [lE] at hfv
    simp only [map_mul, map_sub, map_pow, map_natCast] at hfv ⊢
    linear_combination (-(((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE D)) * hγE' +
      (((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE (W.γA W.gam D)) * hfu +
      algebraMap (LetA O n) W.EE (W.γA W.gam D) * hfv
  have hevD : ∀ ζ, L.ev ζ D ≠ 0 := fun ζ => by
    rw [hDdef, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun t ht => by
      rw [map_pow]; exact pow_ne_zero _ (L.ev_pt t (fun h => hsT (h ▸ ht)) ζ)
  have hevA : ∀ ζ, L.ev ζ D * L.ev ζ (W.γA W.gam U) = L.ev ζ (W.γA W.gam D) * L.ev ζ U := fun ζ => by
    have h1 := congrArg (L.ev ζ) hA
    simp only [map_mul, map_sub, map_pow, map_natCast, L.ev_ps, mul_zero, zero_mul] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hp0))
  let h : Rs L.F PD.p s → L.F := fun ζ => L.ev ζ U / L.ev ζ D
  have hinvΔ : ∀ δ ∈ W.DelF, ∀ ζ, h (powR L.F PD.p s (L.σ δ) ζ) = h ζ := fun δ hδ ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ, hUΔ δ hδ, hDΔ δ hδ]
  have hinvγ : ∀ ζ, h (powR L.F PD.p s (L.σ W.gam) ζ) = h ζ := fun ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ]
    have hγD : L.ev ζ (W.γA W.gam D) ≠ 0 := by rw [L.ev_γ]; exact hevD _
    rw [div_eq_div_iff hγD (hevD ζ)]
    linear_combination hevA ζ
  obtain ⟨c, hc⟩ := hPC L.F PD.p s _ L.gen h (by
    rintro x (rfl | ⟨δ, hδ, rfl⟩)
    · funext ζ; rw [precomp_apply]; exact hinvγ ζ
    · funext ζ; rw [precomp_apply]; exact hinvΔ δ hδ ζ)
  have hUc : ∀ ζ, L.ev ζ U = c * L.ev ζ D := fun ζ => by
    have := hc ζ
    simp only [h] at this
    rw [div_eq_iff (hevD ζ)] at this
    exact this
  obtain ⟨κ1, x, hx⟩ := L.rat U hUΔ D hDΔ hevD c hUc
  set g : LetA O n := ((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D with hgdef
  have hgΔ : g ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) hUΔ)
    (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x) hDΔ)
  have hg0 : ∀ ζ, L.ev ζ g = 0 := fun ζ => by
    rw [hgdef, map_sub, map_mul (L.ev ζ) (((PD.p : ℕ) : LetA O n) ^ κ1) U,
      map_mul (L.ev ζ) (algebraMap O (LetA O n) x) D, map_pow, map_natCast, L.ev_O, hUc ζ, ← hx]
    ring
  obtain ⟨κ2, w, hw, hgw⟩ := L.div g hgΔ hg0
  refine ⟨κ1 + κ2, ((PD.p : ℕ) : O) ^ κ2 * x, w, hw, ?_⟩
  have hlw : letE a * ps W s * w = ps W s * w := by
    calc letE a * ps W s * w = letE a * (ps W s * w) := mul_assoc _ _ _
      _ = letE a * (((PD.p : ℕ) : LetA O n) ^ κ2 * (letE a * g)) := by rw [hgw]
      _ = ((PD.p : ℕ) : LetA O n) ^ κ2 * ((letE a * letE a) * g) := by ring
      _ = ps W s * w := by rw [RatW.letE_idem, hgw]
  rw [hlw, ← hgw]
  have hO : algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ2 * x) =
      algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ κ2 * x)) :=
    IsScalarTower.algebraMap_apply O (LetA O n) W.EE _
  rw [hO]
  simp only [lE, hgdef]
  have hUe' : letE a * (((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D) =
      ((PD.p : ℕ) : LetA O n) ^ κ1 * U - letE a * algebraMap O (LetA O n) x * D := by
    rw [mul_sub, mul_left_comm, hUe, mul_assoc]
  rw [hUe']
  simp only [map_mul, map_sub, map_pow, map_natCast] at hfu ⊢
  linear_combination (((PD.p : ℕ) : W.EE) ^ (κ1 + κ2)) * hfu

end Core

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
