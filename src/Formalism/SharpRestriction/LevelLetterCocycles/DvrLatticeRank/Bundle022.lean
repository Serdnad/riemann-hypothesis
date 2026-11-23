module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle014
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevelValueSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle020
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfDMain
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle008
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle005
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem u2ringPf_zetaO {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) {ζ : ↥LL.1}
    (hζ : IsPrimitiveRoot ζ l) : ∃ z : ↥(OL LL), IsPrimitiveRoot z l := by
  have hv : 0 ≤ P.v LL ζ := by
    have h1 : P.v LL (ζ ^ l) = 0 := by rw [hζ.pow_eq_one, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    cases hq : P.v LL ζ using WithTop.recTopCoe with
    | top =>
      exfalso
      rw [hq] at h1
      obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩
      rw [hk, succ_nsmul, WithTop.add_top] at h1
      exact WithTop.top_ne_zero h1
    | coe q =>
      rw [hq] at h1
      have h2 : ((l • q : ℚ) : WithTop ℚ) = 0 := by rw [WithTop.coe_nsmul]; exact h1
      have h3 : l • q = 0 := by exact_mod_cast h2
      rw [nsmul_eq_mul, mul_eq_zero] at h3
      rcases h3 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero
      · rw [h3]; exact le_refl _
  refine ⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective

theorem u2ring_pf : SecondRingHypothesis := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c
  have hlp : l.Prime := Fact.out
  have : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) :=
    (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := AdicCompletionMax.isAdicComplete_max hp0 hpm
  have hs : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hd := DvdPf.dvdCondition l hl K LL hG
  have hes : eK K * sK l K = ((D.loc l).PD K).p - 1 := by rw [hpl]; exact Nat.mul_div_cancel' hd
  obtain ⟨ζL, hζL⟩ := Formalism.MainNotions.N.zeta_of_good (D.loc l) hG
  obtain ⟨ζ, hζ⟩ := u2ringPf_zetaO (D.loc l) LL hζL
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hpl]; exact hζ
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  obtain ⟨a, r, ha, hrm, hE, hnr⟩ := u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv
  exact u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r
    hrm hE hnr h' hh'

end Formalism.MainNotions.N.Ln34
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

theorem framepf_back (hT : IsCrys PD T.ρ) (Eπ : LetA O n) (h' M : ℕ)
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ) (u : LetA O n) (huΔ : u ∈ W.AΔ)
    (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u) :
    FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ h' M := by
  intro H H' K₁ K₂ lam h₁ h₂
  obtain ⟨βφ, hβφ⟩ := framepf_phiBasis Bs hT
  let eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c) :=
    Module.Basis.ofEquivFun (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu)
  have heb : ∀ j, eb j = framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := fun j => by
    simp only [eb, Module.Basis.coe_ofEquivFun, framepf_ebar]
  have hΨ : ∀ (e : W.EE) j, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ eb j) =
      e • ∑ m, W.φA (framepf_ι π' (c - 1) (H m j)) • W.φD T (Bs.b m) := fun e j => by
    rw [heb, framepf_Ψα_tmul, framepf_hh_ebar, framepf_φD_vec]
  have hΦ : ∀ a : Fin Bs.r → LetA O n,
      framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H' (∑ k, a k • W.φD T (Bs.b k)) =
        ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (H' j k))) ⊗ₜ eb j :=
    fun a => by simp only [heb]; exact framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ H' a
  have hS : ∀ (Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) m k,
      u * W.φA (framepf_ι π' (c - 1) (Km m k)) ∈ W.AΔ := fun Km m k =>
    W.AΔ.mul_mem huΔ (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H',
    framepf_Ψβ_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ hEΔ h' hT H',
    framepf_Ψβ_J Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ h' M hT H',
    framepf_βα_core Bs π' Eπ h' M c huE eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₁) lam (fun j k => ?_) _ _ hΨ hΦ,
    framepf_αβ_core Bs hT π' Eπ h' M c huE hEΔ eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₂) lam (fun j k => ?_) _ _ hΨ hΦ⟩
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₁, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₂, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]

end Local



theorem frame_pf : FrameStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hR h' hh' c
  exact framepf_rec D HW F Cm hA.1 l hl K LL hG π' E hR h' hh' c
    fun T hT Bs hπ0 hΔπ hR2 γ0 hu huE hEΔ u huΔ hφ =>
      framepf_back Bs π' c hπ0 hΔπ hR2 γ0 hu hT _ h' _ huE hEΔ u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem u1r2_pt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    LevelExpansions.V.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hz : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨hQ0, hQ1⟩ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hz
  obtain ⟨-, -, -, p4, -⟩ := hA l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : ∀ i, PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev i 1 letπ) = 0 := fun i => by
    rw [CrystallineExponents.cc_lev_pi _ i 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  refine ⟨hT, ⟨1, by simpa using hz⟩, hz.pow_eq_one, hQ0, hQ1, fun x k hk => ?_,
    fun x hx => ((HW l).W K 1 LL hG).N_φ T x hx⟩
  exact (((p4 T hT).1 (c - 1) 1 ⟨0, one_pow _⟩ (by rw [hX]; exact hπ1 _)).1 x k).2 hk

theorem u1r2_basis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
      (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)), ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k) := by
  classical
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have p9 := (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1
  have h92 := (p9 T hT hs hp2).2.1
  obtain ⟨π₀, E₀, -, hm⟩ := h92
  obtain ⟨⟨r, b, hbΔ, hbu, hbe⟩, -⟩ := hm
  have hw := hp9.2.2.1
  obtain ⟨w₁, hw₁⟩ := hw
  have hs1 : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hBL := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs1 w₁ hw₁ hp9.2.1 b hbΔ hbu hbe c
  obtain ⟨bL⟩ := hBL
  have hsurj : ∀ k, ∃ y : ((HW l).W K 1 LL hG).DD T, ∃ hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1),
      bL k = mkL ((HW l).W K 1 LL hG) T π' c y hy := by
    intro k
    have hq := Submodule.Quotient.mk_surjective _ (bL k)
    obtain ⟨⟨y, hy⟩, hyk⟩ := hq
    exact ⟨y, hy, hyk.symm⟩
  choose rep hrep hbr using hsurj
  exact ⟨r, bL, rep, hrep, hbr⟩

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames

end
end
