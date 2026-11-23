module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open Module Submodule

noncomputable section

namespace Formalism.HN

theorem exists_smul_mem_of_finrank_eq {E : Type*} [AddCommGroup E] (S N : Submodule ℤ E) [Module.Finite ℤ S]
    (hNS : N ≤ S) (hrk : finrank ℤ S = finrank ℤ N) :
    ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N := by
  intro x hx
  set P : Submodule ℤ S := N.comap S.subtype with hP
  have hPr : finrank ℤ P = finrank ℤ N :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hNS)
  have h := P.finrank_quotient_add_finrank
  have h0 : finrank ℤ (S ⧸ P) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem satR_mem_zl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E) (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem real_saturation_property : SatR := by
  intro R V E _ _ _ _ _ _ ρ L N hL hNL
  obtain ⟨hinj, hdisc⟩ := hL
  have : DiscreteTopology (zl ρ L) := hdisc
  have hNL' : zl ρ N ≤ zl ρ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (satR_mem_zl ρ N y).1 hy
    exact (satR_mem_zl ρ L _).2 ⟨x, hNL hx, rfl⟩
  obtain ⟨-, hNS, hrk⟩ := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc hNL'
  set S := Formalism.F.satur (zl ρ L) (zl ρ N) with hSdef
  have : DiscreteTopology S :=
    Formalism.F.discreteTopology_of_le (L := zl ρ L) inf_le_left
  have htor := exists_smul_mem_of_finrank_eq S (zl ρ N) hNS hrk
  have hspan : ∀ y : E, y ∈ S ↔ y ∈ zl ρ L ∧ y ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) :=
    fun y => Submodule.mem_inf
  refine ⟨{ carrier := {x | x ∈ L ∧ ρ x ∈ S}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, ?_, ?_, ?_⟩
  · rintro x y ⟨hxL, hxS⟩ ⟨hyL, hyS⟩
    refine ⟨L.add_mem hxL hyL, ?_⟩
    rw [map_add (f := _)]
    exact S.add_mem hxS hyS
  · refine ⟨L.zero_mem, ?_⟩
    rw [map_zero]
    exact S.zero_mem
  · rintro c x ⟨hxL, hxS⟩
    have hcxL : c • x ∈ L := L.smul_mem c hxL
    refine ⟨hcxL, (hspan _).2 ⟨(satR_mem_zl ρ L _).2 ⟨c • x, hcxL, rfl⟩, ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := htor (ρ x) hxS
    obtain ⟨n, hnN, hn⟩ := (satR_mem_zl ρ N _).1 hax
    have haxL : a • x ∈ L := L.toAddSubgroup.zsmul_mem hxL a
    have hn' : n = a • x := by
      apply hinj (hNL hnN) haxL
      rw [hn, map_zsmul]
    have haxN : a • x ∈ N := hn' ▸ hnN
    have h1 : a • (c • x) ∈ N := by
      rw [smul_comm]
      exact N.smul_mem c haxN
    have h2 : a • ρ (c • x) ∈ zl ρ N := by
      rw [← map_zsmul]
      exact (satR_mem_zl ρ N _).2 ⟨_, h1, rfl⟩
    have h3 : (a : ℝ) • ρ (c • x) ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) := by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.subset_span h2
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have h4 := (span ℝ ((zl ρ N : Submodule ℤ E) : Set E)).smul_mem (a : ℝ)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at h4
  · intro x hx
    exact ⟨hNL hx, hNS ((satR_mem_zl ρ N _).2 ⟨x, hx, rfl⟩)⟩
  · intro x hx
    exact hx.1
  · ext y
    rw [satR_mem_zl]
    constructor
    · rintro ⟨x, ⟨-, hxS⟩, rfl⟩
      exact hxS
    · intro hy
      obtain ⟨x, hxL, rfl⟩ := (satR_mem_zl ρ L _).1 ((hspan y).1 hy).1
      exact ⟨x, ⟨hxL, hy⟩, rfl⟩

end Formalism.HN
end
end

section

open Module NumberField

noncomputable section

namespace Formalism.HN

theorem twist_finrank_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
  have key : Module.finrank ℚ K = 2 * nPl K := by
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := by
      refine ⟨fun w => ?_⟩
      have hc : w.1.IsComplex := IsTotallyComplex.isComplex w.1
      first
        | exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc) w.2
        | exact (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2) hc
    have h3 : Nat.card {w : InfinitePlace K // w.IsComplex} = Nat.card (InfinitePlace K) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
    simp only [Fintype.card_eq_nat_card, Nat.card_of_isEmpty, h3] at h1
    simp only [nPl, Fintype.card_eq_nat_card]
    omega
  exact_mod_cast key

theorem twist_of (h1 : RescaleCovol) (h2 : PlLat) (h3 : ShiftInvariance.{0, 0, 0, 0}) : Twist := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc
  dsimp only
  intro L hL
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    rw [Matrix.det_smul]
    exact ((isUnit_iff_ne_zero.mpr (by exact_mod_cast (hc v).ne' : ((c v : ℂ)) ≠ 0)).pow _).mul (hX v)
  have hfg : ∀ N : Submodule (𝓞 K) V, N ≤ L → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian L hL
    have h1' : (N.comap L.subtype).FG := IsNoetherian.noetherian _
    have h2' := h1'.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2'
  have hnPl : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hfr := twist_finrank_eq K
  have hP : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc v
  have hlogP : Real.log (∏ v, c v) = ∑ v, Real.log (c v) := Real.log_prod fun v _ => (hc v).ne'
  have hkey : ∀ N : Submodule (𝓞 K) V, N ≤ L →
      rk (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N = deg (Formalism.HermitianLatticesTheory.realize b X) N +
        (1 / (nPl K : ℝ)) * (∑ v, Real.log (c v)) * (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
    intro N hN
    have hNfg := hfg N hN
    obtain ⟨hlat, hrk, -⟩ := h2 K V ι b X hX N hNfg
    obtain ⟨-, hrk₂, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' N hNfg
    refine ⟨by rw [hrk, hrk₂], ?_⟩
    have hcov := h1 K V ι b X c hX hc N hNfg
    haveI := hlat.2
    have hC := Formalism.F.covol_pos (zl (Formalism.HermitianLatticesTheory.realize b X) N)
    simp only [deg, Formalism.F.deg]
    rw [hcov, Real.log_mul (Real.rpow_pos_of_pos hP _).ne' hC.ne', Real.log_rpow hP, hlogP, hrk]
    push_cast
    rw [hfr]
    field_simp
    ring
  obtain ⟨hlatL, hrkL, -⟩ := h2 K V ι b X hX L hL
  obtain ⟨hlatL₂, -, -⟩ := h2 K V ι b (fun v => ((c v : ℂ)) • X v) hX' L hL
  obtain ⟨-, hmu, hstep, -⟩ := h3 (𝓞 K) V _ _ (Formalism.HermitianLatticesTheory.realize b X)
    (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L ((1 / (nPl K : ℝ)) * ∑ v, Real.log (c v))
    hlatL hlatL₂ hkey
  have hrkpos : L ≠ ⊥ → (rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) ≠ 0 := by
    intro hne
    rw [hrkL]
    have h1' : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2' : 0 < rkK L := by
      obtain ⟨s, hs⟩ := hL
      unfold rkK
      rw [← hs, Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
      haveI : FiniteDimensional K (Submodule.span K (s : Set V)) := FiniteDimensional.span_finset K s
      rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
      intro h0
      apply hne
      rw [← hs, eq_bot_iff]
      intro x hx
      have hx' := Submodule.span_le_restrictScalars (𝓞 K) K (s : Set V) hx
      have hx0 : x = 0 := by simpa [h0] using hx'
      simp [hx0]
    exact_mod_cast (Nat.mul_pos h1' h2').ne'
  have hslope : L ≠ ⊥ → slope (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) L =
      slope (Formalism.HermitianLatticesTheory.realize b X) L + (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) := by
    intro hne
    have hs : ∀ ρ' : V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        slope ρ' L = deg ρ' L / (rk ρ' L : ℝ) := fun _ => rfl
    rw [hs, hs, (hkey L le_rfl).1, (hkey L le_rfl).2, add_div, mul_div_assoc, div_self (hrkpos hne),
      mul_one]
  refine ⟨hslope, hmu, fun hne => ?_, fun θ => hstep θ⟩
  simp only [muDef, muMaxDef, muMinDef, hslope hne, (hmu hne).1, (hmu hne).2]
  refine ⟨by ring, by ring, by ring⟩

end Formalism.HN
end
end
