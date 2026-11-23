module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle014
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLocC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfNat
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle004
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace Formalism.MainNotions.N.Ln34

theorem u3uplink_pf_of (hW : WStep) : UpSlotOfModels := by
  intro D HW F Cm CA CB CK hA hMF
  exact u3upPf_ofR D HW hMF (hW D HW F Cm CA CB CK hA) (ninlam_pf D HW F Cm CA CB CK hA)
    (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem filC_le_bot (τ : K →ₐ[Qp] LL) (h' : ℕ)
    (hJ : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  by_cases ha : -(h' : ℤ) ≤ a
  · exact u3upPf_FilC_anti (PD := PD) T τ ha
  · have hc : ∀ j : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - j) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - (j + 1 : ℕ)) := by
          intro hj
          have := (hJ _ hj).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        push Not at hnj
        rw [← ih, ← hnj]
        congr 1
        push_cast
        ring
    obtain ⟨j, hj⟩ : ∃ j : ℕ, a = -(h' : ℤ) - j := ⟨(-(h' : ℤ) - a).toNat, by omega⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [hj, hc j]

theorem φD_letter' {i : ZMod n} {x : W.DD T} (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have hφ : W.φA (letE (O := O) i) = letE (i + 1) := by
    funext j
    simp only [LocWach.φA, letφ]
    by_cases h : j = i + 1
    · subst h
      simp [letE]
    · have h' : j - 1 ≠ i := fun h'' => h (by rw [← h'']; ring)
      simp [letE, h, h']
  rw [← hφ, ← algebraMap_smul W.EE (W.φA (letE i)) (W.φD T x)]
  have h : algebraMap (LetA O n) W.EE (W.φA (letE (O := O) i)) =
      W.φE (algebraMap (LetA O n) W.EE (letE i)) := (W.φE_ext _).symm
  rw [h, ← W.φD_smul, algebraMap_smul, hx]

end Generic

end Formalism.MainNotions.N.Ln34.MLC

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem serC_mul {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V'] (f g : PowerSeries LL)
    (d : V') (i : ℤ) :
    serC (f * g) d i = ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k f • serC g d (i - k) := by
  by_cases hi : 0 ≤ i
  · have hsum : ∀ k ∈ Finset.range (i.toNat + 1),
        PowerSeries.coeff k f • serC g d (i - k) =
          (PowerSeries.coeff k f * PowerSeries.coeff (i.toNat - k) g) • d := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : 0 ≤ i - (k : ℤ) := by omega
      have h2 : (i - (k : ℤ)).toNat = i.toNat - k := by omega
      simp only [serC, if_pos h1, h2, mul_smul]
    rw [Finset.sum_congr rfl hsum, ← Finset.sum_smul]
    simp only [serC, if_pos hi]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · have h0 : i.toNat = 0 := by omega
    simp only [serC, if_neg hi, h0, zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero,
      sub_zero, smul_zero]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem expS_mul (c : ZMod n) (ζ : LL) (f : LetA O n) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => f * a j) y i =
      ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k (W.lev c ζ f) • expS W T c ζ a y (i - k) := by
  simp only [expS, map_mul, serC_mul, Finset.smul_sum]
  exact Finset.sum_comm

def GoodF (τ : K →ₐ[Qp] LL) (h' : ℕ) (F : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  ∀ i : ℤ, F i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i)

theorem goodF_mul (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL) (h' : ℕ) (f : LetA O n) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hg : GoodF (PD := PD) T τ h' (expS W T c ζ a y)) :
    GoodF (PD := PD) T τ h' (expS W T c ζ (fun j => f * a j) y) := by
  intro i
  rw [expS_mul]
  refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
  exact u3upPf_FilC_anti (PD := PD) T τ (by omega) (hg (i - k))

end Generic

end Formalism.MainNotions.N.Ln34.MLB

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
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

def FramepfBack {T : LocLat G Qp LL O} (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (Eπ : LetA O n) (h' M : ℕ) : Prop :=
  ∀ (H H' K₁ K₂ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (lam : O),
    H' * H = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₁ →
    H * H' = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₂ →
    ∃ Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c,
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c) ∧
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤,
        Φ (framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x) - lam • x ∈ JLA W T π' Eπ h' M c) ∧
      ∀ y ∈ LamPS W T Eπ h' c,
        framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (Φ y) - lam • y ∈ JP W T π' Eπ h' M c


include Ct in

theorem framepf_data [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (hK : W.gamK = W.gam)
    (Bs : FramepfBas W T) (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hγN : ∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d)
    (Fs : PowerSeries O)
    (hFs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs))
    (hF0 : PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s')
    (hne : ∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) (aσ : O)
    (haσ : ((PD.p : ℕ) : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  have huE := framepf_E_unit hR hs
  have hEΔ := framepf_E_Δ hR
  obtain ⟨Γ, hΓ, R, hΓR⟩ := framepf_Γ Bs π' (c - 1) hπ0 hΔπ hR2 hu hγN
  obtain ⟨H, H', ⟨K1, hK1⟩, ⟨K2, hK2⟩, -, -, ⟨K5, hK5⟩, ⟨K6, hK6⟩⟩ :=
    framepf_mats _ hne Fs hF0 R M hM1 aσ _ haσ
  rw [← pow_mul, mul_comm σ 2] at hK5 hK6
  obtain ⟨Φ, hΦL, hΦJ, hβα, hαβ⟩ := hB H H' K5 K6 _ hK5 hK6
  have hγ := framepf_hhx_γ Bs π' c hπ0 hΔπ hR2 γ0 hu (PowerSeries.X * Fs) (by simp) hFs Γ hΓ H K2 M
    (by rw [hΓR]; exact hK2)
  have hmod := framepf_hhx_mod Bs π' c hπ0 hΔπ hR2 γ0 hu _ H K1 hK1
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero] at h1
    have := W.v_l
    rw [h1, AddValuation.map_zero] at this
    exact absurd this (by simp)
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.1
  refine ⟨_, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H, Φ,
    framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu _ huE hEΔ h' H, hΦL, hγ, hmod,
    framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H, framepf_Ψα_J Bs π' c hπ0 hΔπ hR2 γ0 hu _ h' M H,
    hΦJ, hβα, hαβ, fun x hx hj => ?_, fun x hx hgx => ?_, fun τ ζ hpt x y hxy m a z hrep k hk i hi => ?_⟩
  · exact framepf_JLA_sat π' c (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu) _ h' M hu huE
      (fun o ho => (mul_eq_zero.1 ho).resolve_left hp0) _ x hx hj
  · obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
    obtain ⟨Ff, hFf, -⟩ := hR2 f hfΔ
    obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Ff hFf _ (gradNPf_cc_f W s' w π' f hw hf)
    refine invLiftPf_inj W T π' f t _ hf ht hu hΔπ hγN hK M (fun y hy _ r₀ hr₀ d hd hrd => ?_) x hx
      (by rw [hK]; exact hgx)
    exact invLiftPf_nzd W T π' w s' w.isUnit hw _
      (fun o ho => (mul_eq_zero.1 ho).resolve_left (sub_ne_zero.2 (hne y hy))) Bs.r Bs.b
      (fun j => (Bs.mem j).1) Bs.uniq 1 r₀ d hr₀ hd (by rw [pow_one]; exact hrd)
  · refine framepf_locC Ct T hT hs c ζ (hprim τ ζ hpt) (fun x k hk => ?_) ?_ (fun r hr h => ?_)
      π' _ w w' s' h' M σ hs' hw w'.isUnit hw' hM _
      (fun ℓ => ((mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ)).1) hγ hmod
      _ (framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H) x y hxy m a z hrep k hk i hi
    · exact ((h4.1 (c - 1) 1 ⟨0, one_pow _⟩
        (by rw [Formalism.MainNotions.LiftingTheory.wmap_X_one W hs]; exact framepf_lev_π_one _)).1 x k).2 hk
    · rw [W.gam_gen]
      rw [hs, Nat.cast_one]
      exact zero_le_one
    · obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
      rw [zpow_natCast, ← map_pow, ← map_one (algebraMap O LL)] at h
      apply hne y (by omega)
      rw [← pow_mul, mul_comm, pow_mul, hι h, one_pow]

end Local

end Formalism.MainNotions.N.Ln34

end
end
