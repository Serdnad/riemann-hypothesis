module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle002
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Lemmata.GeneralBFactSecondTail.Imports
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField NumberField.InfinitePlace

noncomputable section

namespace Formalism.HN

theorem sizeMu_rpow_eq (f J C d : ℝ) (hf : 0 < f) (hJ : 0 < J) (hC : 0 < C) (hd : 0 < d) :
    ((2 : ℝ) ^ (f * J) * d ^ (-J / 2) * C) ^ ((1 : ℝ) / (2 * f * J)) =
      Real.exp (Real.log 2 / 2 - Real.log d / (2 * (2 * f)) - (-Real.log C) / ((2 * f) * J)) := by
  have h2 : (0 : ℝ) < 2 ^ (f * J) := Real.rpow_pos_of_pos two_pos _
  have hd' : 0 < d ^ (-J / 2) := Real.rpow_pos_of_pos hd _
  rw [Real.rpow_def_of_pos (mul_pos (mul_pos h2 hd') hC), Real.log_mul (mul_pos h2 hd').ne' hC.ne',
    Real.log_mul h2.ne' hd'.ne', Real.log_rpow two_pos, Real.log_rpow hd]
  congr 1
  field_simp
  ring

theorem sizeMu_finrank_eq (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * nPl K := by
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

theorem sizeMu_of (h1 : PlLat) : SizeMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX L hLfg hL0 c
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  have hnf := sizeMu_finrank_eq K
  have hd : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  obtain ⟨hlat, hrkL, hhtL⟩ := h1 K V ι b X hX L hLfg
  have hSB := saturation_basic_properties (𝓞 K) V _ ρ L hlat

  have hrk_pos : ∀ N : Submodule (𝓞 K) V, N.FG → N ≠ ⊥ →
      0 < (nPl K : ℝ) ∧ 0 < (rkK N : ℝ) := by
    intro N hN hN0
    obtain ⟨hlN, hrkN, -⟩ := h1 K V ι b X hX N hN
    have h0 : rk ρ N ≠ 0 := fun h =>
      hN0 (((saturation_basic_properties (𝓞 K) V _ ρ N hlN).2.2.2.1 N le_rfl).1 h)
    rw [hrkN, hnf] at h0
    constructor
    · have : nPl K ≠ 0 := fun h => h0 (by simp [h])
      exact_mod_cast Nat.pos_of_ne_zero this
    · have : rkK N ≠ 0 := fun h => h0 (by simp [h])
      exact_mod_cast Nat.pos_of_ne_zero this

  have hsize : ∀ N : Submodule (𝓞 K) V, N.FG → N ≠ ⊥ →
      size b X N = Real.exp (c - slope ρ N) := by
    intro N hN hN0
    obtain ⟨hf, hj⟩ := hrk_pos N hN hN0
    obtain ⟨hlN, hrkN, -⟩ := h1 K V ι b X hX N hN
    have hC : 0 < Formalism.F.covol (zl ρ N) := by
      have := hlN.2
      exact Formalism.F.covol_pos _
    unfold size ht
    rw [show (2 : ℝ) ^ (nPl K * rkK N) = (2 : ℝ) ^ ((nPl K : ℝ) * (rkK N : ℝ)) by
      rw [← Real.rpow_natCast]; push_cast; rfl]
    rw [sizeMu_rpow_eq _ _ _ _ hf hj hC hd]
    congr 1
    have hr : (Formalism.F.rk (zl ρ N) : ℝ) = 2 * (nPl K : ℝ) * rkK N := by
      have : Formalism.F.rk (zl ρ N) = 2 * nPl K * rkK N := by
        rw [← hnf]; exact hrkN
      rw [this]; push_cast; ring
    simp only [c, slope, Formalism.F.slope, Formalism.F.deg, logDisc, hr, hnf]
    push_cast
    ring

  have hlt_of : ∀ S : Submodule (𝓞 K) V, IsSat ρ L S → S ≠ L → rk ρ S < rk ρ L := by
    intro S hS hSL
    obtain ⟨-, hSle, -⟩ := hSB.2.2.2.2.2.2.2 S hS
    rcases lt_or_eq_of_le hSle with h | h
    · exact h
    · exact absurd (hSB.2.2.1 S L hS hS.1 le_rfl h.symm).symm hSL

  have hsizeQ : ∀ S : Submodule (𝓞 K) V, IsSat ρ L S → S ≠ L →
      sizeQ b X L S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ S))) := by
    intro S hS hSL
    have hSfg : S.FG := Submodule.FG.of_le hLfg hS.1
    obtain ⟨-, hrkS, -⟩ := h1 K V ι b X hX S hSfg
    obtain ⟨hqrk, hSle, -⟩ := hSB.2.2.2.2.2.2.2 S hS
    have hlt := hlt_of S hS hSL
    have hf := (hrk_pos L hLfg hL0).1
    have hjlt : (rkK S : ℝ) < rkK L := by
      rw [hrkS, hrkL, hnf] at hlt
      have : rkK S < rkK L := Nat.lt_of_mul_lt_mul_left hlt
      exact_mod_cast this
    have hJ : 0 < (rkK L : ℝ) - rkK S := by linarith
    have hCq : 0 < Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ S)) := by
      have := (Formalism.F.degQuot _ (zl ρ L) (zl ρ S) hlat.2 hS.2).1
      exact Formalism.F.covol_pos _
    unfold sizeQ htQ
    rw [sizeMu_rpow_eq _ _ _ _ hf hJ hCq hd]
    congr 1
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) : ℝ) =
        2 * (nPl K : ℝ) * ((rkK L : ℝ) - rkK S) := by
      rw [hqrk, Nat.cast_sub hSle, hrkS, hrkL, hnf]
      push_cast; ring
    simp only [c, Formalism.F.slope, Formalism.F.deg, logDisc, hr, hnf]
    push_cast
    ring
  have hMC := slope_characterization (𝓞 K) V _ ρ L hlat hL0
  refine ⟨hsize L hLfg hL0, ?_, hsizeQ, ?_, ?_, ?_⟩
  ·
    rw [hsize L hLfg hL0, Real.log_exp]
    simp only [muDef, c]
    ring
  ·
    obtain ⟨N, hNs, hN0, hNslope⟩ := hMC.2.2.1
    have hbound : ∀ R : Submodule (𝓞 K) V, R ≤ L → R ≠ ⊥ → slope ρ R ≤ muMax ρ L := by
      intro R hRL hR0
      have h := (hMC.1 (muMax ρ L)).1 le_rfl R hRL
      have hRfg : R.FG := Submodule.FG.of_le hLfg hRL
      obtain ⟨hf, hj⟩ := hrk_pos R hRfg hR0
      obtain ⟨-, hrkR, -⟩ := h1 K V ι b X hX R hRfg
      have hpos : (0 : ℝ) < rk ρ R := by rw [hrkR, hnf]; push_cast; positivity
      show deg ρ R / (rk ρ R : ℝ) ≤ _
      rw [div_le_iff₀ hpos]
      exact h
    unfold leastSize
    apply IsLeast.csInf_eq
    refine ⟨⟨N, hNs.1, hN0, ?_⟩, ?_⟩
    · rw [hsize N (Submodule.FG.of_le hLfg hNs.1) hN0, hNslope]
    · rintro t ⟨R, hRL, hR0, rfl⟩
      rw [hsize R (Submodule.FG.of_le hLfg hRL) hR0]
      exact Real.exp_le_exp.2 (by linarith [hbound R hRL hR0])
  ·
    unfold largestSize
    have hset : {t | ∃ S : Submodule (𝓞 K) V, IsSat ρ L S ∧ S ≠ L ∧ sizeQ b X L S = t} =
        (fun s => Real.exp (c - s)) '' {t | ∃ N : Submodule (𝓞 K) V, IsSat ρ L N ∧ N ≠ L ∧
          Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N)) = t} := by
      ext t
      constructor
      · rintro ⟨S, hS, hSL, rfl⟩
        exact ⟨_, ⟨S, hS, hSL, rfl⟩, (hsizeQ S hS hSL).symm⟩
      · rintro ⟨s, ⟨S, hS, hSL, rfl⟩, rfl⟩
        exact ⟨S, hS, hSL, hsizeQ S hS hSL⟩
    rw [hset]
    refine (Antitone.map_csInf_of_continuousAt (f := fun s => Real.exp (c - s)) ?_ ?_ ?_ ?_).symm
    · exact (Real.continuous_exp.comp (continuous_const.sub continuous_id)).continuousAt
    · intro a a' haa
      exact Real.exp_le_exp.2 (by linarith)
    · exact ⟨_, ⊥, hSB.2.2.2.2.2.1, fun h => hL0 h.symm, rfl⟩
    · refine ⟨muMin ρ L, ?_⟩
      rintro t ⟨S, hS, hSL, rfl⟩
      have h := (hMC.2.1 (muMin ρ L)).1 le_rfl S hS.1
      obtain ⟨hqrk, hSle, hqdeg⟩ := hSB.2.2.2.2.2.2.2 S hS
      have hlt : (rk ρ S : ℝ) < rk ρ L := by exact_mod_cast hlt_of S hS hSL
      show _ ≤ Formalism.F.deg _ / (Formalism.F.rk _ : ℝ)
      rw [hqrk, hqdeg, Nat.cast_sub hSle, le_div_iff₀ (by linarith)]
      exact h
  ·
    intro L' hLL' hL'fg hrk'
    obtain ⟨hlat', hrkL', -⟩ := h1 K V ι b X hX L' hL'fg
    unfold ht
    rw [hrk']
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Formalism.F.covolAntiSameRank _ (zl ρ L) (zl ρ L') hlat'.2 (muChar_zl_mono ρ hLL')
      (by show rk ρ L = rk ρ L'; rw [hrkL, hrkL', hrk'])

theorem size_maximal_slope : SizeMu := by
  exact sizeMu_of place_lattice_structure

end Formalism.HN
end
end

section

open Module NumberField

noncomputable section

namespace Formalism.HN

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem sizeIneq_exists_mul_mem (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> first | assumption | infer_instance)

theorem sizeIneq_span_inf_ker (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hxA, hxk⟩
    exact ⟨Submodule.subset_span hxA, hxk⟩
  · rintro x ⟨hxS, hxk⟩
    obtain ⟨d, hd, hdx⟩ := sizeIneq_exists_mul_mem A x hxS
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
    have hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨hdx, ?_⟩
      show φ (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]
    have hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem sizeIneq_rk [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by
  unfold rkK
  set S := Submodule.span K (A : Set V) with hS
  have h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      S.map φ := by
    rw [Submodule.map_coe, hS, Submodule.map_span]
    rfl
  rw [h1, sizeIneq_span_inf_ker]
  have := (φ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]
  congr 1
  exact (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm

end SlopeTestRemainingChoices

theorem sizeIneq_of (h1 : SizeMu) (h2 : HtImage) (h3 : PlLat) : SizeIneq := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hIB hI0
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀def
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hA0 : A ≠ ⊥ := by
    intro h
    apply hI0
    rw [hIdef, h, Submodule.map_bot]
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hAlat, -, -⟩ := h3 K V ι b X hX A hAfg
  obtain ⟨hBlat, -, -⟩ := h3 K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, hhtI⟩ := h3 K W κ b' X' hX' I hIfg
  obtain ⟨hsat, hht⟩ := h2 K V ι W κ b X b' X' hX hX' φ A hAfg
  have hSA := h1 K V ι b X hX A hAfg hA0
  have hSB := h1 K W κ b' X' hX' B hBfg hB0
  obtain ⟨-, -, hsQ, -, hlarge, -⟩ := hSA
  obtain ⟨-, -, -, hleast, -, -⟩ := hSB
  have hSI := (h1 K W κ b' X' hX' I hIfg hI0).1

  have hA₀ne : A₀ ≠ A := by
    intro h
    apply hI0
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    have hx0 : x ∈ A₀ := h ▸ hx
    exact (Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx0.2)

  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hdegI := (hMB.1 (muMax ρ' B)).1 le_rfl I hIB
  have hslI : slope ρ' I ≤ muMax ρ' B := by
    show Formalism.F.deg (zl ρ' I) / (Formalism.F.rk (zl ρ' I) : ℝ) ≤ _
    rw [div_le_iff₀ (by exact_mod_cast hrkIpos)]
    exact hdegI
  have hleI : leastSize b' X' B ≤ size b' X' I := by
    rw [hleast, hSI]
    exact Real.exp_le_exp.2 (by linarith)

  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 A₀ hsat
  have hlt : rk ρ A₀ < rk ρ A := by
    refine lt_of_le_of_ne hq.2.1 (fun h => hA₀ne ?_)
    exact (hSBA.2.2.1 A₀ A hsat hsat.1 le_rfl h.symm).symm
  have hMA := slope_characterization (𝓞 K) V _ ρ A hAlat hA0
  have hmin := (hMA.2.1 (muMin ρ A)).1 le_rfl A₀ hsat.1
  have hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ A₀)) := by
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ A₀)) : ℝ) = (rk ρ A : ℝ) - rk ρ A₀ := by
      rw [hq.1, Nat.cast_sub hq.2.1]
    have hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ A₀ := by
      have : (rk ρ A₀ : ℝ) < rk ρ A := by exact_mod_cast hlt
      linarith
    unfold Formalism.F.slope
    rw [hr, le_div_iff₀ hrpos, hq.2.2]
    exact hmin
  have hQle : sizeQ b X A A₀ ≤ largestSize b X A := by
    rw [hlarge, hsQ A₀ hsat hA₀ne]
    exact Real.exp_le_exp.2 (by linarith)
  have hlargepos : 0 < largestSize b X A := by rw [hlarge]; exact Real.exp_pos _

  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    have : rkK I ≠ 0 := by
      intro h
      rw [hrkI, h, mul_zero] at hrkIpos
      exact lt_irrefl _ hrkIpos
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrkR : ((rkK A : ℝ) - rkK A₀) = rkK I := by
    rw [← hrkeq]; push_cast; ring
  rw [Finset.prod_pow] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A A₀ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A A₀) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [div_le_iff₀ hlargepos]
  calc leastSize b' X' B ≤ size b' X' I := hleI
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := hcore
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * largestSize b X A :=
        mul_le_mul_of_nonneg_left hQle (Real.rpow_nonneg hP _)

end Formalism.HN
end
end
