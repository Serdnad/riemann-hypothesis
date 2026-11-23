module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.UnivLinkPf

theorem univLinkPf_deep_sub {up : Bool} {bτ S η h' : ℕ} (hb : η < bτ) (hS : bτ + S ≤ h') :
    deep up bτ S ∪ Set.Icc (-(η : ℤ)) η ⊆ Set.Icc (-(h' : ℤ)) h' := by
  intro a ha
  rcases ha with ha | ⟨h1, h2⟩
  · unfold deep at ha
    split_ifs at ha
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := ha
      exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩



theorem univlink_pf : UnivLinkStep := by
  intro D HW Fo hA hd hR hC hH hMF hU1 hk hU2 hDn hUp hMx
  intro l _ hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b hN c
  obtain ⟨hc₁, hc₂, -, hJ₁, hJ₂, hηb, hbS, hh', -, hposition⟩ := id hN
  have hj₁ : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₁ τ a ha)
  have hj₂ : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') :=
    fun τ a ha => univLinkPf_deep_sub (hηb τ) (hbS τ) (hJ₂ τ a ha)
  have hs : 1 ≤ sK l K := by
    have hdv := hd l hl K LL hG
    have hlp : l.Prime := Fact.out
    have h2 := hlp.two_le
    have hpos : 0 < l - 1 := by omega
    have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_dvd_iff] at hdv
      omega
    exact Nat.div_pos (Nat.le_of_dvd hpos hdv) he
  have hM : 1 ≤ MK l K h' := by
    have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
      have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
    exact Nat.ceil_pos.2 (div_pos h4 hs')
  obtain ⟨α, β, hfr⟩ := hH l hl K LL hG π' E hp9 h' hh' c
  have hU3 : ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
      (MK l K h') S up b c (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)) α := by
    rcases hposition with h2 | hsl
    · exact hMx l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN h2
    · by_cases hex : ∃ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c ∧ up τ = true
      · obtain ⟨τ₀, hτ₀, hu₀⟩ := hex
        exact universal_lift_mono_exponent _ F (hUp l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => (hsl τ τ₀ (hτ.trans hτ₀.symm)).trans hu₀) _
      · refine universal_lift_mono_exponent _ F (hDn l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr hN
          fun τ hτ => ?_) _
        cases h : up τ
        · rfl
        · exact absurd ⟨τ, hτ, h⟩ hex
  obtain ⟨s₀, hcard, hsub, hmain⟩ := univLinkPf_local ((HW l).W K 1 LL hG) F hc₁ hc₂
    ((hA l K 1 LL hG).2.1 (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hl)) (hfr.1 T₂ hc₂ hj₂).2.2.2.1
    (hMF l hl K LL hG π' E hp9 h' hh' c α β hfr T₂ hc₂ hj₂) hM
    (hR l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hR l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hC l hl K LL hG π' E hp9 T₁ h' hh' hc₁ hj₁ c) (hC l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c)
    (hk l hl K LL hG π' E hp9 h' S up b c (fun τ => by have := hηb τ; omega) hbS)
    (hU1 l hl K LL hG π' E hp9 T₁ T₂ F S η m h' up b c α β hfr) hN
    (hU2 l hl K LL hG π' E hp9 T₂ h' hh' hc₂ hj₂ c) hU3
  refine ⟨s₀, hcard, hsub, fun x hx => ?_⟩
  have h := hmain x hx
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at h
  have hexp : sigA l (sK l K) h' + y2K l K h' S η = sigA l (sK l K) h' +
      (2 * sigA l (sK l K) h' + kapA l (eK K) h' S +
        (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η))) := by
    unfold y2K; ring
  rw [hexp, ← Nat.cast_smul_eq_nsmul ↥(OL LL), Nat.cast_pow]
  exact h

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ExtPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem extPf_filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp :=
    fun x hx => PD.Fil_anti a hx
  unfold FilV
  rintro _ ⟨t, rfl⟩
  refine ⟨AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) t, ?_⟩
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
  rfl

theorem extPf_fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (extPf_filV_succ_le PD (LL := LL) (V := V) a)

theorem extPf_multV_eq_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem extPf_not_jump (τ : K →ₐ[Qp] LL) (hfin : Module.Finite LL ↥(DdRE PD ρ τ)) (a : ℤ)
    (h : multV PD ρ τ a = 0) : ¬ IsJumpV PD ρ τ a := by
  intro hj
  unfold IsJumpV at hj
  apply hj
  haveI : FiniteDimensional LL ↥(DdRE PD ρ τ) := hfin
  have hsub : FildR PD ρ τ a ≤ DdRE PD ρ τ := by
    unfold FildR
    exact inf_le_left
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le hsub
  apply Submodule.eq_of_le_of_finrank_eq (extPf_fildR_succ_le PD ρ τ a)
  unfold multV at h
  omega

end Gen

theorem ext_pf : Formalism.MainNotions.N.Ln34.ExtStep := by
  intro D HW F Cm CA CB CK hA l _ _ K LL hG T h' hh' hc hj κ hκ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h8, h11, -⟩ := hA
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨h1, hz⟩ := Formalism.MainNotions.LiftingTheory.lone_HOne0 ((HW l).W K 1 LL hG)
  obtain ⟨Tp, ι, π, hcp, hext⟩ := Formalism.MainNotions.LiftingTheory.lext_HExt_D D HW F l K 1 LL hG h1 T κ hc hκ
  refine ⟨Tp, ι, π, hext, hcp, h1, fun τ a ha => ?_⟩
  by_contra hout
  obtain ⟨-, -, hadd⟩ := h11 l K LL T Tp ((HW l).W K 1 LL hG).one ι π hext.1 hcp
  have hfin := ((h8 l K LL Tp).2 τ).1
  have h0 : multV ((D.loc l).PD K) T.ρ τ a = 0 :=
    extPf_multV_eq_zero _ _ τ a fun hT => hout (hj τ a hT)
  have h2 : multV ((D.loc l).PD K) ((HW l).W K 1 LL hG).one.ρ τ a = 0 := by
    refine extPf_multV_eq_zero _ _ τ a fun hO => hout ?_
    rw [hz τ a hO]
    exact Set.mem_Icc.2 ⟨by omega, by omega⟩
  exact extPf_not_jump _ _ τ hfin a (by have := hadd τ a; omega) ha

end Formalism.MainNotions.N.Ln34.ExtPf

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.OneGenPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem onegen_pf : Formalism.MainNotions.N.Ln34.OneGenStep := by
  intro D HW F Cm CA CB CK _ l _ _ K LL hG
  obtain ⟨-, -, e, -, hspan, hφ, hγ⟩ := Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hG
  exact ⟨e, hspan, hφ, hγ⟩

end Formalism.MainNotions.N.Ln34.OneGenPf
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section KerLam2Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private theorem kl2_dec_lemma (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (a : LetA O n) (s : W.DD T) (hs : s ∈ S) :
    ∃ t : Fin PD.p → W.DD T, (∀ k, t k ∈ S) ∧
      a • W.φD T s = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (t k) := by
  obtain ⟨e, he⟩ := Formalism.MainNotions.LiftingTheory.PhiBasis_of W a
  refine ⟨fun k => e k • s, fun k => S.smul_mem _ hs, ?_⟩
  rw [he, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, mul_smul]

theorem frobenius_span_decomposition (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (z : W.DD T)
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T S) :
    ∃ s : Fin PD.p → W.DD T, (∀ k, s k ∈ S) ∧
      z = ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (s k) := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := kl2_dec_lemma W T S 1 s hs
    exact ⟨t, ht, by rw [← he, one_smul]⟩
  | zero => exact ⟨fun _ => 0, fun _ => S.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨fun k => s k + s' k, fun k => S.add_mem (hs k) (hs' k),
      by simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    choose t ht he using fun k : Fin PD.p =>
      kl2_dec_lemma W T S (a * (letπ : LetA O n) ^ (k : ℕ)) (s k) (hs k)
    refine ⟨fun j => ∑ k, t k j, fun j => S.sum_mem fun k _ => ht k j, ?_⟩

    simp only [Finset.smul_sum, ← mul_smul, he, map_sum]
    rw [Finset.sum_comm]

theorem frobenius_span_exact_lift (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (c'' : IsCrys PD T''.ρ) (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T) (i : ZMod n)
    (z : W.DD Tp) (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Tp (W.Nl Tp i)) (h0 : W.map π z = 0) :
    ∃ z' ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i), W.map ι z' = z := by
  obtain ⟨s, hs, rfl⟩ := frobenius_span_decomposition W Tp (W.Nl Tp i) z hz
  have hπs : ∀ k, W.map π (s k) = 0 := by
    refine Formalism.MainNotions.LiftingTheory.phii_DD W T'' c'' (fun k => W.map π (s k)) ?_

    rw [← h0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ]
  choose y hy using fun k => hex (s k) (hπs k)
  have hyNl : ∀ k, y k ∈ W.Nl T i := by
    intro k
    obtain ⟨w, hw, hwe⟩ := (Formalism.MainNotions.LiftingTheory.wmap_mem_Nl W Tp i (s k)).1 (hs k)
    have hyN : y k ∈ W.N T := by
      apply h4
      rw [hy k, ← hwe]
      exact (W.N Tp).smul_mem _ hw
    rw [Formalism.MainNotions.LiftingTheory.wmap_mem_Nl]
    refine ⟨y k, hyN, ?_⟩
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hy k, Formalism.MainNotions.LiftingTheory.wmap_Nl_fix W Tp i (s k) (hs k)]
  refine ⟨∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (y k), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
    exact Submodule.subset_span ⟨y k, hyNl k, rfl⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, W.map_φ, hy k]

theorem frobenius_span_exact_local (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    {T Tp T'' : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L T''.L)
    (π' Eπ : LetA O n) (h' : ℕ) (c'' : IsCrys PD T''.ρ)
    (hinj : Function.Injective (W.map ι))
    (hex : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (h4 : ∀ x : W.DD T, W.map ι x ∈ W.N Tp → x ∈ W.N T)
    (hπ' : IsUnit (algebraMap (LetA O n) W.EE π')) :
    KerLam W ι π π' Eπ h' := by
  have hex' : ∀ x, W.map π x = 0 → ∃ y, W.map ι y = x := fun x hx => (hex x).1 hx
  have hΔ : ∀ x : W.DD T, (∀ δ ∈ W.DelF, W.γD Tp δ (W.map ι x) = W.map ι x) →
      ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro x hx δ hδ
    apply hinj
    rw [W.map_γ, hx δ hδ]
  have hL : ∀ (x : W.DD T) (a : LetA O n), a • W.map ι x = W.map ι x → a • x = x := by
    intro x a hx
    apply hinj
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hx]
  refine ⟨hinj, ?_, fun c => ⟨?_, ?_⟩⟩
  · intro k y hy hyπ
    rw [mem_PiNS] at hy
    obtain ⟨⟨y0, hy0N, rfl⟩, hyΔ⟩ := hy
    have hz : W.map π y0 = 0 := by
      have hu : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
        rw [map_pow]
        exact hπ'.pow k
      rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, ← algebraMap_smul W.EE] at hyπ
      exact (hu.smul_eq_zero).1 hyπ
    obtain ⟨x0, rfl⟩ := hex' y0 hz
    refine ⟨π' ^ k • x0, ?_, Formalism.MainNotions.LiftingTheory.wmap_map_smul W ι _ _⟩
    rw [mem_PiNS]
    refine ⟨⟨x0, h4 x0 hy0N, rfl⟩, hΔ _ ?_⟩
    rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul]
    exact hyΔ
  · intro y hy hyπ
    rw [mem_LamPS] at hy
    obtain ⟨hyE, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    obtain ⟨z', hz', hz'e⟩ := frobenius_span_exact_lift W ι π c'' hinj hex' h4 (c - 1) (Eπ ^ h' • W.map ι x) hyE
      (by rw [Formalism.MainNotions.LiftingTheory.wmap_map_smul, hyπ, smul_zero])
    refine ⟨x, ?_, rfl⟩
    rw [mem_LamPS]
    refine ⟨?_, hΔ x hyΔ, hL x _ hyL⟩
    have e : z' = Eπ ^ h' • x := hinj (by rw [hz'e, Formalism.MainNotions.LiftingTheory.wmap_map_smul])
    rw [← e]
    exact hz'
  · intro y hy hyπ
    rw [mem_NcS] at hy
    obtain ⟨hyN, hyΔ, hyL⟩ := hy
    obtain ⟨x, rfl⟩ := hex' y hyπ
    refine ⟨x, ?_, rfl⟩
    rw [mem_NcS]
    exact ⟨h4 x hyN, hΔ x hyΔ, hL x _ hyL⟩

end KerLam2Local

theorem kerlam2_pf : KerLamStep := by
  unfold KerLamStep kerLamR
  intro D HW F Cm CA CB CK hA hF l _ hl K LL hG π' E hp9 T Tp T'' ι π h' hses hT hTp hT'' hJ
  obtain ⟨hW, -⟩ := hA
  obtain ⟨-, -, -, -, -, h6W, -⟩ := hW l K 1 LL hG
  obtain ⟨-, -, h6ses⟩ := h6W
  obtain ⟨-, -, -, hsat, -⟩ := h6ses T Tp T'' ι π hT hTp hT'' hses
  have hEx := hF l K 1 LL hG T Tp T'' ι π hses
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := hp9
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  letI : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [e]
    exact Formalism.MainNotions.LiftingTheory.phib_OL_complete LL
  refine frobenius_span_exact_local _ ι π π' _ h' hT'' hEx.1 hEx.2.2 hsat ?_
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (by simpa using (Formalism.MainNotions.LiftingTheory.wmap_unit _ 0).pow _)

end Formalism.MainNotions.N.Ln34

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

theorem gampi_delta {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gamK x - x) = W.γD T W.gamK x - x := by
  intro δ hδ
  rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

theorem gampi_letter (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T W.gamK x - x ∈ letS W T c := by
  have hl : letγ (W.γ₀ W.gamK) (letE c : LetA O n) = letE c := by
    funext j
    show W.γ₀ W.gamK ((letE c : LetA O n) j) = (letE c : LetA O n) j
    rcases eq_or_ne j c with rfl | h
    · simp [letE]
    · simp [letE, Pi.single_apply, h]
  have key : ∀ y : W.DD T, W.γD T W.gamK ((letE c : LetA O n) • y) = (letE c : LetA O n) • W.γD T W.gamK y := by
    intro y
    rw [← algebraMap_smul W.EE (letE c : LetA O n) y, W.γD_smul, W.γE_ext, hl, algebraMap_smul]
  unfold letS at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hx ⊢
  rw [smul_sub, ← key, sub_eq_zero.1 hx, sub_self]

theorem gampi_local (π' π'₀ u : LetA O n) (hu : π'₀ = u * π')
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γD T W.gamK x - x = π'₀ • x') :
    GamPi W T π' := by
  intro c x hx
  unfold NcS at hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxN, hxD⟩, hxL⟩ := hx
  rw [Submodule.restrictScalars_mem] at hxN
  have hxfix : ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro δ hδ
    unfold DelS at hxD
    have h1 := (Submodule.mem_iInf _).1 hxD δ
    have h2 := (Submodule.mem_iInf _).1 h1 hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
    exact h2
  have hxΔ : x ∈ W.NΔ T := show x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x from ⟨hxN, hxfix⟩
  obtain ⟨x', hx'mem, hx'⟩ := hm x hxΔ
  have hx'N : x' ∈ W.N T := (show x' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x' = x' from hx'mem).1
  rw [Submodule.mem_inf]
  refine ⟨?_, gampi_letter W T c hxL⟩
  unfold PiNS
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    unfold Formalism.MainNotions.DeltaInvariantLattices.aN
    refine Submodule.mem_map.2 ⟨u • x', (W.N T).smul_mem u hx'N, ?_⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
    rw [LinearMap.smul_apply, LinearMap.id_apply, hx', hu, pow_one, smul_smul, mul_comm]
  · unfold DelS
    rw [Submodule.mem_iInf]
    intro δ
    rw [Submodule.mem_iInf]
    intro hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact gampi_delta W T hxfix δ hδ

end Local

theorem gamPiCondition : GamPiStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T hcrys
  have hT1 := hA.1 l K 1 LL hG
  have hP9 := hT1.2.2.2.2.2.2.2.2.1
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hp]; exact hl
  obtain ⟨-, ⟨π₁, E₁, hr₁, hm₁⟩, -⟩ := hP9 T hcrys hs1 hp2
  obtain ⟨w₁, hw₁⟩ := hr₁.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2
  refine gampi_local _ T π' π₁ ((w₁ * w⁻¹ : (LetA _ _)ˣ) : LetA _ _) ?_ ?_
  · rw [hw₁, hw, hp, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  · intro x hx
    obtain ⟨x', hx', h⟩ := hm₁.2 x hx
    exact ⟨x', hx', by rw [hgam]; exact h⟩

end Formalism.MainNotions.N.Ln34

end
end
