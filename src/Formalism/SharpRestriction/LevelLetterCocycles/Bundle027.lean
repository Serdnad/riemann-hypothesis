module

import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle005
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

private theorem isPrecomplete_of_module_finite {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [hR : IsPrecomplete I R] [Module.Finite R M] : IsPrecomplete I M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨fun g hg => ?_⟩
  have hd : ∀ k, g (k + 1) - g k ∈ I ^ k • Submodule.span R (Set.range s) := by
    intro k
    rw [hs]
    have h := SModEq.sub_mem.1 (hg (Nat.le_succ k))
    have h2 := neg_mem h
    rwa [neg_sub] at h2
  choose A hA hAs using fun k =>
    (Submodule.mem_ideal_smul_span_iff_exists_sum (I ^ k) s (g (k + 1) - g k)).1 (hd k)
  have hc : ∀ i : Fin n, ∀ {a b : ℕ}, a ≤ b →
      (∑ k ∈ Finset.range a, A k i) ≡ (∑ k ∈ Finset.range b, A k i) [SMOD (I ^ a • ⊤ : Submodule R R)] := by
    intro i a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Finset.sum_range_add_sum_Ico _ hab,
      sub_add_cancel_left]
    refine neg_mem (sum_mem fun k hk => ?_)
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1 (hA k i)
  choose C hC using fun i : Fin n => hR.prec' _ (hc i)
  refine ⟨g 0 + ∑ i, C i • s i, fun K => ?_⟩
  rw [SModEq.sub_mem]
  have hgK : g K = g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
    have h1 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) = g K - g 0 := Finset.sum_range_sub g K
    have h2 : ∑ k ∈ Finset.range K, (g (k + 1) - g k) =
        ∑ i, (∑ k ∈ Finset.range K, A k i) • s i := by
      simp only [← hAs, Finsupp.sum_fintype, zero_smul, implies_true, Finset.sum_smul]
      exact Finset.sum_comm
    rw [← h2, h1]
    abel
  rw [hgK]
  have hsplit : g 0 + ∑ i, (∑ k ∈ Finset.range K, A k i) • s i - (g 0 + ∑ i, C i • s i) =
      ∑ i, ((∑ k ∈ Finset.range K, A k i) - C i) • s i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  refine sum_mem fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h := SModEq.sub_mem.1 (hC i K)
  rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h



theorem complete_max {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  apply Formalism.MainNotions.N.Ln17.isAdicComplete_integers_local <;> assumption

theorem lemmaDN0_L (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 ((HW l).W K 1 LL hg) := by
  intro l _ K LL hg _
  have hT := h1 l K 1 LL hg
  obtain ⟨hE, hC, hQ⟩ := h11 l K LL
  have := complete_max LL
  have h9D : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l' _ K' s' LL' h' => (h1 l' K' s' LL' h').2.2.2.2.2.2.2.2.1
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F h9D
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lemmaDN0_of_admits _ hE hC hQ (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg) hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.2.2.2.1 ?_ ?_
  · intro hA hl11 c ζ hζ
    have hK : K.1 ≤ MaximalUnramifiedExtension l := by
      intro x hx
      obtain ⟨y, hy⟩ := hA.1.2 ⟨x, hx⟩
      have hyx : ((y : ↥(K0 K)) : Om l) = x := congrArg (fun z : ↥K.1 => (z : Om l)) hy
      rw [← hyx]
      exact y.2.2
    have hAD : CaseA K LL := ⟨hK, by rw [← hp]; exact hA.2.2, hg⟩
    have h5l : 5 ≤ l := by rw [← hp]; omega
    obtain ⟨τ, hτ⟩ := hpt l K LL hAD h5l c ζ (by rwa [hp] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  · rw [hp]
    exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev
end
end

section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

def KillLevFacts (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => LevGrad ((HW l).W K 1 LL hG)

theorem annihilator_levels_of_grading (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hK : KillLevFacts D HW) : KillerLevelsTheorem D HW F Cm := by
  rintro ⟨-, h9⟩
  intro l _ K LL hG hC h5
  have hfd : FiniteDimensional (Padic l) ↥(K0 K) := by
    first
    | exact inferInstance
    | exact ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank (Padic l) ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hC
  have hT := tool_algebra_of_ring_condition D HW F h9 l K LL hC h5
  exact KL.killerLevCore_of _ (KF.psUnitE_of _ hR hT) (KF.psCoprime_of _ hR) (hK l K LL hG hC h5)
    (KF.psStable_of _ hR) hR.1

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

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem finiteDimensional_filLev (c : ZMod n) (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (u : ℤ) :
    FiniteDimensional LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 u) := by
  have hc : c - ((0 : ℕ) : ZMod n) = c := by simp
  haveI : FiniteDimensional LL
      ↥(Formalism.WeaklyAdmissibleFiltrations.FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - ((0 : ℕ) : ZMod n)))) := by
    rw [hc]
    exact Submodule.finiteDimensional_of_le inf_le_right
  unfold Formalism.MainNotions.WachCoordinates.FilLev
  infer_instance

theorem multV_nonneg' [NeZero n] (hFD : Sh.FilDim W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (k : ℤ) : 0 ≤ multV PD T.ρ τ k := by
  obtain ⟨-, hdim⟩ := hFD hA T hT c τ hτ
  have h1 := hdim k (k + 1) (by omega)
  have hI : Finset.Ico k (k + 1) = {k} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton] at h1

  have hle : Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1) ≤ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k := by
    unfold Formalism.MainNotions.WachCoordinates.FilLev
    apply Submodule.map_mono
    apply Submodule.map_mono
    apply inf_le_inf_right
    unfold Formalism.WeaklyAdmissibleFiltrations.FilCris
    apply inf_le_inf_left
    apply Submodule.comap_mono
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
  haveI := finiteDimensional_filLev W T c hfd k
  have h2 : Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) :=
    LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  have h3 : ((Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) : ℕ) : ℤ) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) := by exact_mod_cast h2
  linarith

theorem sum_multV_le [NeZero n] (hFD : Sh.FilDim W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (c : ZMod n) (hc : c ∈ evens n d) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c) (a : ℕ) (ha : a < b c) :
    ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T₂.ρ τ k ≤ (m : ℤ) := by
  have hjump := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  have hfd := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ Finset.Icc (-(η : ℤ)) η)]
  · calc ∑ k ∈ (Finset.Ico (-(a : ℤ)) 0).filter (fun k => k ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ k
        ≤ ∑ k ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
            (fun k _ _ => multV_nonneg' W T₂ hFD hS.1 hT₂ c τ hτ hfd k)
      _ ≤ (m : ℤ) := hS.2.2.2.2.2.2.2.1 c τ hτ
  · intro k hk hne
    have hj : IsJumpV PD T₂.ρ τ k := by
      by_contra hnj
      exact hne (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T₂.ρ τ k hnj)
    have hw := hjump k hj
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    have hk' := Finset.mem_Ico.1 hk
    simp only [Finset.mem_Icc]
    omega

theorem step1Pass_pass [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W)
    (hFD : Sh.FilDim W) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) [IsDomain O] [IsPrincipalIdealRing O]
    [IsFractionRing O LL] {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (u : FF →ₗ[O] W.DD T) (a m : ℕ)
    (hu : ∀ f, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (u f) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ a • u f ∈ W.N T ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (u f) - u f))
    (hdim : ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T.ρ τ k ≤ (m : ℤ)) :
    (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, u f ∈ W.N T) ∧ (m = 0 → ∀ f, u f ∈ W.N T) := by
  have hlev : W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W ^ a) ≠ 0 := by
    obtain ⟨⟨w, hw, hq⟩, -, -⟩ := hER hA c ζ hζ
    rw [map_pow, hq, mul_pow]
    exact mul_ne_zero (pow_ne_zero _ hw.ne_zero) (pow_ne_zero _ PowerSeries.X_ne_zero)
  have R := hEx hA T hT c ζ hζ
  have hex : ∀ f, ∃! d, Sh.IsExp W T c ζ (u f) d := fun f => R.1 (u f) _ (hu f).2.1 hlev
  choose ex hexs huniq using hex
  have ex_add : ∀ f g, ex (f + g) = ex f + ex g := fun f g =>
    (huniq (f + g) _ (by rw [map_add (f := _)]; exact R.2.2.1 _ _ _ _ (hexs f) (hexs g))).symm
  have ex_smul : ∀ (r : O) f, ex (r • f) = fun k => algebraMap O LL r • ex f k := fun r f =>
    (huniq (r • f) _ (by rw [map_smul]; exact R.2.2.2.1 r _ _ (hexs f))).symm
  set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 0 with hF0
  set Fa := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(a : ℤ)) with hFa
  let φ : FF →+ (T.V ⊗[Qp] BdR) ⧸ F0 :=
    AddMonoidHom.mk' (fun f => Submodule.Quotient.mk (ex f 0)) (fun f g => by
      simp only [ex_add, Pi.add_apply, Submodule.Quotient.mk_add])
  have hφ : ∀ (r : O) f, φ (r • f) = algebraMap O LL r • φ f := by
    intro r f
    simp only [φ, AddMonoidHom.mk'_apply, ex_smul, Submodule.Quotient.mk_smul]
  have hLK : ∀ f, ex f 0 ∈ Fa ∧ (u f ∈ W.N T ↔ ex f 0 ∈ F0) := by
    intro f
    have hj : ∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T (u f) - u f) ∈ W.N T := by
      obtain ⟨y, hy, -, he⟩ := (hu f).2.2
      exact ⟨0, by rw [pow_zero, one_smul, he]; exact (W.N T).smul_mem _ hy⟩
    exact (hK hA T hT c ζ hζ (u f) (ex f) (hu f).1 (hexs f) hj).2 a (hu f).2.1
  have hker : ∀ f, φ f = 0 ↔ u f ∈ W.N T := by
    intro f
    rw [(hLK f).2]
    exact Submodule.Quotient.mk_eq_zero _
  have := finiteDimensional_filLev W T c hfd (-(a : ℤ))
  have := finiteDimensional_filLev W T c hfd 0
  let Aq := Fa.map F0.mkQ
  have hle : F0 ≤ Fa := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0 (by omega : -(a : ℤ) ≤ 0)
  have hAq : finrank LL ↥Aq ≤ m := by
    let g := F0.mkQ ∘ₗ Fa.subtype
    have hr : LinearMap.range g = Aq := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker g = F0.comap Fa.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
    have h2 := (hFD hA T hT c τ hτ).2 (-(a : ℤ)) 0 (by omega)
    rw [← hF0, ← hFa] at h2
    omega
  have hrange : ∀ f, φ f ∈ Aq := fun f => Submodule.mem_map_of_mem (hLK f).1
  refine ⟨fun lenO cc A => ?_, fun hm0 f => ?_⟩
  · let φA : ↥A →+ (T.V ⊗[Qp] BdR) ⧸ F0 := φ.comp A.subtype.toAddMonoidHom
    have hφA : ∀ (r : O) (x : ↥A), φA (r • x) = algebraMap O LL r • φA x := fun r x => hφ r x
    have hm : finrank LL ↥(Submodule.span LL (Set.range φA)) ≤ m := by
      have : FiniteDimensional LL ↥Aq := inferInstance
      refine le_trans (Submodule.finrank_mono ?_) hAq
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hrange x
    refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.zeroSub A φA hφA,
      Formalism.MainNotions.N.Pv.LocalLengthBound.pchain_of_gen (Formalism.MainNotions.N.Pv.LocalLengthBound.pstep_rank A φA hφA hm), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hker _).1 hy
  · subst hm0
    have h0 : Aq = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have := hrange f
    rw [h0, Submodule.mem_bot] at this
    exact (hker f).1 this

end Pass

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem local_theorem_of_leaf_lemmas (hG : GenStep) (hL : LiftStep) (hd : DvdStep) (hq : QuotStep)
    (hn : NormStep) (h9 : DeltaInvariantUniformizer) (he : ExtStep) (hw : WStep) (hk : KerLamStep) (hl : NinLamStep)
    (hg : GradNStep) (hf : FrobPiNStep) (hγ : GamPiStep) (ho : OneGenStep)
    (hUL : UnivLinkStep) (hR : InvLiftStep) (hC : ClassMapStep) (hH : FrameStep)
    (hMFL : ModelFLinkStep) (hP5 : ExpansionFormHypothesis) (hML : ModelLStep) (hMQL : ModelQLinkStep)
    (hU1L : FirstFrameOfModels) (hkp : KapPiStep) (hU2L : SecondPropositionOfRank) (hU2R : SecondRankHypothesis)
    (hD : DownSlotOfModels) (hUp : UpSlotOfModels) (hMx : MixedSlotOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC160 hFont hdr hrk hA
  have hMQ : ModelQStep := modelQStep_of hMQL hML
  have hU2 : SecondPropositionHypothesis := second_proposition_of_models hU2L hMQ hU2R hML
  have hMF := modelFStep_of hMFL hP5 D HW F Cm CA CB CK hdr hrk hA
  have hU1 := first_frame_of_models hU1L hML D HW F Cm CA CB CK hdr hrk hA hMF
  have hUniv : univR D HW :=
    hUL D HW F hA.2.2.2.2.1 hd (hR D HW F Cm CA CB CK hA) (hC D HW F Cm CA CB CK hA)
      (hH D HW F Cm CA CB CK hA) hMF hU1 (hkp D HW F Cm CA CB CK hA) (hU2 D HW F Cm CA CB CK hA)
      (hD D HW F Cm CA CB CK hA hMF) (hUp D HW F Cm CA CB CK hA hMF) (hMx D HW F Cm CA CB CK hA hdr hrk hMF)
  have hKill : killR D :=
    killR_of_steps D HW hd (hq D hA.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.2.1) (hn D)
      (h9 D HW F Cm hA.1)
      (splitR_of_steps D HW F hA.2.1 hA.2.2.2.2.1 (he D HW F Cm CA CB CK hA) (hw D HW F Cm CA CB CK hA)
        (hk D HW F Cm CA CB CK hA hFont) (hl D HW F Cm CA CB CK hA) (hg D HW F Cm CA CB CK hA)
        (hf D HW F Cm CA CB CK hA) (hγ D HW F Cm CA CB CK hA) (ho D HW F Cm CA CB CK hA))
      hUniv
  exact local_theorem_of_good_extensions D C hC160 (local_form_of_three_inputs D (hG D HW F Cm CA CB CK hA) (hL D HW F Cm CA CB CK hA) hKill)

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finiteDimensional_max_unramified (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h : K0 K ≤ K.1 := inf_le_left
  exact FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion h).injective

theorem fd_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos _
  have hfin : Set.Finite {x : Om l | x ^ (l ^ s) = 1} :=
    (Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset fun x hx => by
      simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := hfin.to_subtype
  haveI : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hpos (by rw [hx]; exact isIntegral_one)
  haveI := finiteDimensional_max_unramified K
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

def bigLL (K LL : FinExt l) : FinExt l :=
  ⟨LL.1 ⊔ IntermediateField.normalClosure ℚ_[l] ↥(Ks K 1) (Om l), by
    have := LL.2
    have := fd_Ks K 1
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_bigLL (K LL : FinExt l) : LL.1 ≤ (bigLL K LL).1 := le_sup_left

theorem unram_of_caseA {K LL : FinExt l} (hA : CaseA K LL) :
    Function.Bijective (algebraMap ↥(K0 K) ↥K.1) := by
  refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun y => ⟨⟨y, ⟨y.2, hA.1 y.2⟩⟩, ?_⟩⟩
  apply Subtype.ext
  rfl

def BrRest {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)
    [Fintype (K →ₐ[Qp] LL)] : Prop :=
  ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem brHyp2_of_rec (P : LocPrime l) {K LL : FinExt l} (hA : CaseA K LL) (h5 : 5 ≤ l)
    [NeZero (finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))) (hs : W.s = 1) {Cc : ℝ}
    (h5W : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6W : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9W : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hwx : Formalism.MainNotions.LiftingTheory.coreWX W) (hwr : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (htools : ToolsAlg W) (hf1 : F1 W) (hf2 : F2 W) (hH : HodgeExact (P.PD K) ↥LL.1 ↥(OL LL))
    (hrest : BrRest W) : BrHyp2 W Cc := by
  refine ⟨hs, unram_of_caseA hA, ?_, h5W, h6W, h9W, h2a, hwx, hwr, htools, hf1, hf2, hH, ?_, ?_, hrest⟩
  · rw [P.PD_p K]
    exact h5
  · unfold ValRing
    refine ⟨fun a b h => Subtype.ext h, fun x hx => ⟨⟨x, (P.v_O LL x).1 hx⟩, rfl⟩, fun o => ?_⟩
    exact (P.v_O LL _).2 o.2
  · rw [P.PD_p K]
    exact complete_OL LL

end Formalism.MainNotions.WachCoordinates.Br
end
end
