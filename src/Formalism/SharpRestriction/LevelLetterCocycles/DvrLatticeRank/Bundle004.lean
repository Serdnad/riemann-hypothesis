module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle003
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLK

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module



theorem lev_Eat_simple (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    ∃ U : PowerSeries ↥LL.1, ((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = PowerSeries.X * U ∧
      PowerSeries.constantCoeff U ≠ 0 := by
  obtain ⟨τs, hIs, -⟩ := hpt
  obtain ⟨-, hIs2⟩ := hIs
  unfold Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations at hr
  obtain ⟨-, -, -, -, ⟨w, hw⟩, -, -, -⟩ := hr
  generalize (HW l).W K 1 LL hG = W at hw ⊢

  have hz : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rw [(D.loc l).ζQ_zero] at h
    simpa using h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show (D.loc l).ζQ 1 ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    exact SetLike.le_def.mp le_sup_right (IntermediateField.subset_adjoin ℚ_[l] _ (by simpa using hz))
  have hζ : τs ⟨_, hmem⟩ = ζ := hIs2 ⟨_, hmem⟩ rfl
  have hζl : ζ ^ l = 1 := by
    have h1 : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz)
    rw [← hζ, ← map_pow, h1, map_one]
  have hne : ζ ≠ 1 := by
    intro h1
    have h2 : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 :=
      RingHom.injective (τs : ↥(Ks K 1) →+* ↥LL.1) (by simp [hζ, h1])
    exact (D.loc l).ζQ_one (by simpa using congrArg Subtype.val h2)
  have hprim : IsPrimitiveRoot ζ l := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζl hne] at h
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have h' := (D.loc l).v_l LL
    rw [h, AddValuation.map_zero] at h'
    simp at h'

  obtain ⟨F, hF0, hFd, hFπ⟩ :=
    W.lev_π c ζ ⟨1, by rw [(D.loc l).PD_p K, pow_one]; exact hprim⟩
  obtain ⟨F1, hF1⟩ : PowerSeries.X ∣ F - 1 := by
    rw [PowerSeries.X_dvd_iff, map_sub, hF0, map_one, sub_self]
  have hF1c : PowerSeries.constantCoeff F1 = 1 := by
    have hd := congrArg (fun f : PowerSeries ↥LL.1 => PowerSeries.constantCoeff (PowerSeries.derivative f)) hF1
    simp only [map_sub, Derivation.map_one_eq_zero, sub_zero, hFd, hF0, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, map_add, map_mul, map_one, PowerSeries.constantCoeff_X,
      zero_mul, zero_add, mul_one] at hd
    exact hd.symm

  have hq : (letπ : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) * W.q =
      (1 + letπ) ^ ((D.loc l).PD K).p - 1 := by
    funext i
    exact W.q₀_def
  have hl1 : W.lev c ζ 1 = 1 := map_one (W.lev c ζ)
  have hadd : W.lev c ζ (1 + letπ) = 1 + W.lev c ζ letπ := by
    rw [← hl1]
    exact (W.lev c ζ).map_add 1 letπ
  have hlq := congrArg (W.lev c ζ) hq
  rw [map_mul (W.lev c ζ), map_sub (W.lev c ζ), map_pow (W.lev c ζ), hadd, hl1, hFπ, (D.loc l).PD_p K, mul_pow, ← map_pow PowerSeries.C ζ l, hζl,
    map_one PowerSeries.C, one_mul, ← mul_geom_sum, hF1, hw, map_mul (W.lev c ζ)] at hlq
  have hy0 : PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by
    have h := congrArg PowerSeries.constantCoeff hFπ
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hF0, mul_one] at h
    have h' : PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by linear_combination h
    rw [h']
    exact sub_ne_zero.mpr hne
  obtain ⟨u, hu⟩ : IsUnit (W.lev c ζ letπ * W.lev c ζ ↑w) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hy0)).mul
      (w.isUnit.map (W.lev c ζ))
  rw [← mul_assoc, ← hu] at hlq
  refine ⟨↑u⁻¹ * (F1 * ∑ i ∈ Finset.range l, F ^ i), ?_, ?_⟩
  · calc _ = ↑u⁻¹ * (↑u * W.lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hlq]; ring
  · rw [map_mul]
    refine mul_ne_zero ((u⁻¹).isUnit.map PowerSeries.constantCoeff).ne_zero ?_

    rw [map_mul, hF1c, one_mul, map_sum]
    simpa [hF0] using hl0

end Formalism.MainNotions.N.Ln34.MLK
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
    (W : LocWach PD LL O v n)

theorem gradNPf_cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  exact Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a

theorem gradNPf_γA_comm (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  exact Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a

theorem gradNPf_cc_f (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hf : W.γA W.gam π' = π' * f) (i : ZMod n) :
    PowerSeries.constantCoeff (f i) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  have hi := congrFun hf i
  have hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i) := rfl
  have hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X *
      PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X)) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1)
      (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  rw [hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow] at hi
  have h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
      (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') =
      PowerSeries.X ^ s' * ((w : LetA O n) i * f i) := by
    linear_combination hi
  have h3 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)
  rw [map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀] at h3
  have hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) :=
    (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff
  exact (hwu.mul_left_cancel h3).symm

theorem gradNPf_fΔ (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hf : W.γA W.gam π' = π' * f) : ∀ δ ∈ W.DelF, W.γA δ f = f := by
  intro δ hδ
  have hu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    have hl : IsUnit (algebraMap (LetA O n) W.EE letπ) := by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0
    exact (w.isUnit.map _).mul (hl.pow _)
  apply Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu
  have h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π' := by
    rw [Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]
  rw [hf, map_mul, hπΔ δ hδ] at h1
  exact h1

theorem gradNPf_expand (π' a : LetA O n) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (F : ZMod n → PowerSeries O) (hF : ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (c₀ : O) (hc : ∀ i, PowerSeries.constantCoeff (a i) = c₀) :
    ∃ t : LetA O n, a - algebraMap O (LetA O n) c₀ = π' * t := by
  have hS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  refine ⟨fun i => PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩
  funext i
  have e1 : a i = π' i * PowerSeries.subst (π' i)
      (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) +
      PowerSeries.C (PowerSeries.constantCoeff (F i)) := by
    conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]
    rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
      PowerSeries.subst_C]
    rfl
  have e3 : PowerSeries.constantCoeff (F i) = c₀ := by
    have := congrArg PowerSeries.constantCoeff e1
    rw [hc i, map_add (f := _), map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
    exact this.symm
  rw [e3] at e1
  have hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀ := by
    rw [PowerSeries.algebraMap_apply]
    rfl
  show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))
  rw [hC, e1]
  ring

theorem exists_gam_pi_factor (T : LocLat G Qp LL O) (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n)
    (E : ZMod n → Polynomial O) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n)
    (w₀ : (LetA O n)ˣ) (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s')
    (hm : ∀ y ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T y - y = π'₀ • x') :
    ∃ f t : LetA O n, W.γA W.gam π' = π' * f ∧
      f - algebraMap O (LetA O n) (((W.χΓ W.gam : Oˣ) : O) ^ s') = π' * t ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π' := fun δ hδ => hR.1 δ hδ
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.2.1
  obtain ⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := ⟨_, rfl⟩
  have hf : W.γA W.gam π' = π' * f := by
    rw [hfdef]
    linear_combination hw'
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)
  refine ⟨f, t, hf, ht, ?_, hπΔ, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · intro y hy
    obtain ⟨x', hx', hxe⟩ := hm y hy
    refine ⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩
    have hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π' := by
      rw [hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
    rw [smul_smul, mul_comm π', ← hπ₀]
    exact hxe

end Local



theorem gradNPf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hs : 1 ≤ sK l K) :
    ∃ (f t : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x u : ↥(OL LL)),
      IsUnit u ∧ x - 1 = (l : ↥(OL LL)) * u ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * f ∧
      f - algebraMap ↥(OL LL) (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x ^ sK l K) = π' * t ∧
      IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
      (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
      (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
        ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
      ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
      ∀ N : ℕ, ∃ a : ↥(OL LL), (l : ↥(OL LL)) ^ (N + padicValNat l N.factorial) =
        a * ∏ y ∈ Finset.Ico 1 (N + 1), ((x ^ sK l K) ^ y - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  obtain ⟨f, t, hf, ht, hEE, hπΔ, hγN⟩ :=
    exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact ⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp,
    fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu
      (sK l K) (by omega) hsl N⟩

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.CyclotomicLifting

theorem padicValNat_le_of_dvd' (p : ℕ) {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b := by
  by_cases hp1 : p = 1
  · subst hp1
    first
      | simp
      | simp [padicValNat]
      | (unfold padicValNat; simp)
  · nth_rw 2 [Nat.padicValNat_def]
    have hd : p ^ padicValNat p a ∣ b := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hab
    have hf : FiniteMultiplicity p b := Nat.finiteMultiplicity_iff.2 ⟨hp1, Nat.pos_of_ne_zero hb⟩
    first
      | exact hf.le_multiplicity_of_pow_dvd hd
      | exact (hf.pow_dvd_iff_le_multiplicity).mp hd

theorem ePB_le_expLift_pf (l M H h : ℕ) (jumps : Finset ℤ) (hM : M ≤ h) (hH : H ≤ 2 * h) :
    Formalism.MainNotions.LiftingTheory.ePB l 1 M H jumps ≤ expLift l h (Formalism.MainNotions.LiftingTheory.JSet jumps M) := by
  unfold Formalism.MainNotions.LiftingTheory.ePB expLift LiftingTheory.eWB LIFT.eU
  have h1 : padicValNat l (2 * H).factorial ≤ padicValNat l (2 * (2 * h)).factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_ne_zero _)
  have h2 : padicValNat l M.factorial ≤ padicValNat l h.factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial hM) (Nat.factorial_ne_zero _)
  omega

theorem JSet_sub_pf (jumps : Finset ℤ) (M h : ℕ) (hj : ∀ a ∈ jumps, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hM : M ≤ h) :
    Formalism.MainNotions.LiftingTheory.JSet jumps M ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧
      (0 : ℤ) ∉ Formalism.MainNotions.LiftingTheory.JSet jumps M := by
  unfold Formalism.MainNotions.LiftingTheory.JSet
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
      obtain ⟨ha1, ha2⟩ := hj _ ha
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · exact (Finset.mem_filter.mp h0).2 rfl
    · have h1 := (Finset.mem_Icc.mp h0).1
      omega

theorem pow_smul_mem_of_le {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O M) (p : O) {e e' : ℕ} (he : e ≤ e') {c : M} (hc : p ^ e • c ∈ S) :
    p ^ e' • c ∈ S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact S.smul_mem _ hc

theorem jumpSet_bound {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (M h : ℕ) (hM : M ≤ h) : ∀ a ∈ Formalism.MainNotions.LiftingTheory.jumpSet W T M M, -(h : ℤ) ≤ a ∧ a ≤ h := by
  classical
  unfold Formalism.MainNotions.LiftingTheory.jumpSet
  intro a ha
  have ha' : a ∈ Finset.Icc (-(M : ℤ)) M := by
    first
      | exact Finset.mem_of_mem_filter a ha
      | (simp only [Finset.mem_filter] at ha; exact ha.1)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha'
  constructor <;> omega

theorem lift_jumps_bounded {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (Fm : LatHom T₁.L T₂.L) (h n : ℕ)
    (Js : Finset ℤ) (hJb : ∀ a ∈ Js, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hL : Fm.LiftF (P.PD K) (Formalism.MainNotions.LiftingTheory.ePB l 1 (Formalism.MainNotions.LiftingTheory.Mmax n fun _ => h)
      (Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) fun _ => h) Js)) :
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      Fm.LiftF (P.PD K) (expLift l h J) := by
  have hMm : Formalism.MainNotions.LiftingTheory.Mmax n (fun _ => h) ≤ h := by
    unfold Formalism.MainNotions.LiftingTheory.Mmax
    exact Finset.sup_le fun _ _ => le_rfl
  have hHm : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) (fun _ => h) ≤ 2 * h := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    exact Finset.sup_le fun _ _ => by dsimp only; omega
  obtain ⟨hJ1, hJ2⟩ := JSet_sub_pf Js _ h hJb hMm
  refine ⟨_, hJ1, hJ2, ?_⟩
  have he := ePB_le_expLift_pf l _ _ h Js hMm hHm
  unfold Formalism.WeaklyAdmissibleFiltrations.LatHom.LiftF at hL ⊢
  intro c hc
  exact pow_smul_mem_of_le _ _ he (hL c hc)

theorem lift_bound_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) : liftR D := by
  obtain ⟨-, -, -, -, -, -, hA4, -, -, -, hA8, -, hA12⟩ := hA
  obtain ⟨-, -, -, -, hDesc⟩ := hA4
  intro l _ hl K LL hg T₁ T₂ Fm r S η m h up b hH
  have hKK : K.1 ≤ (cycL K).1 := hg.2.2.1
  have hle : GK (cycL K) ≤ GK K := GK_le hKK
  have hg1 : Good (cycL K) 1 LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · rw [Ks_cycL K]; exact le_rfl
    · rw [Ks_cycL K]; exact hg.2.2.2
  have hD := hDesc l (cycL K) K hKK hle (GKin_normal K hKK) 1 LL hg1
  have hs : ((HW l).W (cycL K) 1 LL hg1).s = 1 := (HW l).W_s _ _ _ _
  have hCB : Formalism.MainNotions.LiftingTheory.CaseB ((HW l).W (cycL K) 1 LL hg1) := by
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [((HW l).W (cycL K) 1 LL hg1).GKs_def, hs, Nat.cast_one, (D.loc l).PD_χ,
        ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]
      exact v_ge_one _ LL _ (chi_cong (D.loc l) K g g.2)
    · rw [(D.loc l).PD_p, hs, finrank_cycL]
      simp
  have hv0 := hD.2 hCB rfl (by rw [max_unramified_cyclotomic_eq K]; exact inf_le_left)
  have hrange : (Subgroup.inclusion hle).range.Normal := by
    rw [range_inclusion_eq K hKK hle]
    exact GKin_normal K hKK
  have hres := hA12 l (cycL K) K hKK hle LL T₁ hH.1
  have hres2 := hA12 l (cycL K) K hKK hle LL T₂ hH.2.1
  have hL := (hD.1 hrange T₁ T₂ Fm (fun _ => h) (fun _ => h) ⟨hres.1, hres2.1, hH.2.2.1⟩
    (by
      intro i τ _ a ha
      have hm := multV_ne_zero (D.loc l) (cycL K) LL _ τ a ((hA8 l (cycL K) LL _).2 τ).1 ha
      rw [hres.2 τ a] at hm
      have := hH.2.2.2.2.2.2.2.1 (τ.comp (IntermediateField.inclusion hKK)) a
        (isJump_of_multV (D.loc l) K LL T₁ _ a hm)
      simpa using this)).2 hCB
  rw [(D.loc l).PD_p, hv0, add_zero, hs] at hL
  exact lift_jumps_bounded (D.loc l) K LL Fm h _ _
    (jumpSet_bound (D.loc l) (cycL K) LL _ _ _ h (Finset.sup_le fun _ _ => le_rfl)) hL

end Formalism.MainNotions.N.Ln34

end
end
