module

import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle123
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle121
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Matrix

def sgnIx {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem sgnIx_mul_self {p q : ℕ} (a : Ix p q) : sgnIx a * sgnIx a = 1 := by
  cases a <;> simp [sgnIx]

theorem star_sgnIx {p q : ℕ} (a : Ix p q) : star (sgnIx a) = sgnIx a := by
  cases a <;> simp [sgnIx]

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnIx := by
  unfold Jm Formalism.UG.Jpq
  ext (i | i) (j | j) <;> simp [sgnIx, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem adjZ_apply {p q : ℕ} (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = sgnIx a * sgnIx b * star (Z b a) := by
  unfold adjZ
  rw [Jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  ring

theorem adjZ_adjZ {p q : ℕ} (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  ext a b
  rw [adjZ_apply, adjZ_apply, star_mul', star_mul', star_sgnIx, star_sgnIx, star_star]
  have ha := sgnIx_mul_self a
  have hb := sgnIx_mul_self b
  linear_combination (sgnIx b * sgnIx b * Z a b) * ha + Z a b * hb

theorem adjZ_add {p q : ℕ} (Y Z : Mat p q) : adjZ (Y + Z) = adjZ Y + adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.add_apply, star_add]
  ring

theorem adjZ_smul {p q : ℕ} (c : ℂ) (Z : Mat p q) : adjZ (c • Z) = star c • adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
  ring

theorem adjZ_Eab {p q : ℕ} (a b : Ix p q) : adjZ (Eab a b) = (sgnIx a * sgnIx b) • Eab b a := by
  ext i j
  rw [adjZ_apply]
  simp only [Eab, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, star_one]
    ring
  · have h' : ¬ (b = i ∧ a = j) := fun h'' => h ⟨h''.2, h''.1⟩
    rw [if_neg h, if_neg h', star_zero]
    ring

private theorem Jm_mul_JmRealPlaceTaylor (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq_diagonal, Matrix.diagonal_mul_diagonal]
  have h : (fun a : Ix p q => sgnIx a * sgnIx a) = fun _ => 1 := funext sgnIx_mul_self
  rw [h, Matrix.diagonal_one]

theorem mem_upq_iff {p q : ℕ} (Z : Mat p q) : Z ∈ upq p q ↔ adjZ Z = -Z := by
  have hJ := Jm_mul_JmRealPlaceTaylor p q
  show Zᴴ * Jm p q + Jm p q * Z = 0 ↔ _
  unfold adjZ
  constructor
  · intro h
    have h2 : Jm p q * (Zᴴ * Jm p q + Jm p q * Z) = 0 := by rw [h, mul_zero]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hJ, one_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  · intro h
    have h2 : Jm p q * (Jm p q * Zᴴ * Jm p q) = Jm p q * (-Z) := by rw [h]
    rw [← mul_assoc, ← mul_assoc, hJ, one_mul, mul_neg] at h2
    rw [h2]
    abel

private theorem sameBlock_symm_twisted_operators {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> exact h

theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (h : IsKC Z) : IsKC (adjZ Z) := by
  have h' : ∀ a b, ¬ sameBlock a b → Z a b = 0 := h
  intro a b hab
  have hba : ¬ sameBlock b a := fun hs => hab (sameBlock_symm_twisted_operators hs)
  rw [adjZ_apply, h' b a hba, star_zero, mul_zero]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> trivial

theorem exists_upq_add {p q : ℕ} (Z : Mat p q) :
    ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  apply GlobalTheory.CoverDS.exists_decomp <;> assumption

theorem hasDerivAt_orbit {p q : ℕ} {T : GrpData p q} (πU : URep T) {Y : Mat p q} (hY : Y ∈ upq p q)
    {x y : πU.H} (h : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) (πU.π (T.expt (t • Y)) y) t := by
  have h0 : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y (t - t) := by
    rwa [sub_self]
  have h1 := HasDerivAt.comp_sub_const t t h0
  have h2 := ((πU.π (T.expt (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
  convert h2 using 1
  funext s
  have e : T.expt (s • Y) = T.expt (t • Y) * T.expt ((s - t) • Y) := by
    have hs : t + (s - t) = s := by ring
    rw [← T.expt_add Y hY, hs]
  simp only [Function.comp, e, map_mul]
  rfl

theorem inner_pi_pi {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  let e : πU.H →ₗᵢ[ℂ] πU.H := ⟨(πU.π g : πU.H →ₗ[ℂ] πU.H), πU.isom g⟩
  exact e.inner_map_map x y

theorem inner_pi_left {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) y = inner ℂ x (πU.π g⁻¹ y) := by
  have e : πU.π g (πU.π g⁻¹ y) = y := by
    show (πU.π g * πU.π g⁻¹) y = y
    rw [← map_mul]
    simp
  have h := inner_pi_pi πU g x (πU.π g⁻¹ y)
  rwa [e] at h

end GlobalTheory.FockTensor
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspApproxCompact

theorem isCuspFun_of_approx (D : D7) (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (ha : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ : GA D V → ℂ, Continuous ψ ∧
      (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧ ∀ h ∈ C, ‖f h - ψ h‖ < δ) :
    IsCuspFun V f := by
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g := by
    have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    exact continuous_subtype_val.mul continuous_const
  have hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K) :=
    hK.image hcont
  have h1 := hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g
  have hfin : μ 𝓕 < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have hM0 : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕 := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψl, hψcusp, hψ⟩ := ha _ hC δ hδ
    have h0 := (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g
    have hfi := hint f hf hl W hW μ hμ 𝓕 h𝓕 g
    have hψi := hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢
    have e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ := by
      rw [integral_sub hfi hψi, h0, sub_zero]
    rw [e]
    refine norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc n
    have hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V := by
      rw [GlobalTheory.AutFunCompare.GQ_eq]
      exact Subgroup.mem_subgroupOf.1 hγ
    have ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) =
        f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) -
          ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']
    rw [ee]
    exact (hψ _ ⟨_, hk, rfl⟩).le
  by_contra hne
  have hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ := norm_pos_iff.2 hne
  have := key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

end GlobalTheory.CuspApproxCompact
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.measure_parahoricDatumSupport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (r : ℕ) (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E],
    MeasurableSet {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} ∧
    (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real {x | InSupp x} = volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ := by
  first | exact @GlobalTheory.SupportVolume.measure_support | exact GlobalTheory.SupportVolume.measure_support | (intros; apply GlobalTheory.SupportVolume.measure_support <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory.CoefHeight

open Polynomial

theorem val_coeff_prod_X_sub_C_le {K : Type} [Field K] (w : Valuation K ℝ≥0) {M : ℝ≥0} (hM : 1 ≤ M)
    (s : Multiset K) (hs : ∀ z ∈ s, w z ≤ M) (j : ℕ) :
    w ((s.map fun a => X - C a).prod.coeff j) ≤ M ^ Multiset.card s := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    have ha : w a ≤ M := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ z ∈ s, w z ≤ M := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine (w.map_sub _ _).trans (max_le ?_ ?_)
    · cases j with
      | zero => rw [coeff_X_mul_zero, map_zero]; exact bot_le
      | succ i => rw [coeff_X_mul]; exact (ih hs' i).trans (pow_le_pow_right₀ hM (Nat.le_succ _))
    · rw [map_mul, pow_succ']
      exact mul_le_mul' ha (ih hs' j)

theorem nnnorm_coeff_minpoly_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (v : HeightOneSpectrum (𝓞 F)) (j : ℕ) :
    ‖algebraMap F (v.adicCompletion F) ((minpoly F x).coeff j)‖₊ ≤
      max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x)) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set q := p.map (algebraMap F (FvBar F v)) with hqdef
  have hmon : q.Monic := (minpoly.monic hint).map _
  have hsplit : q.Splits := IsAlgClosed.splits q
  have hq : q = (q.roots.map fun a => X - C a).prod := hsplit.eq_prod_roots_of_monic hmon
  have hroots : ∀ z ∈ q.roots, valBar F v z ≤ M := by
    intro z hz
    have hq0 : q ≠ 0 := hmon.ne_zero
    have hz' : aeval z p = 0 := by
      rw [mem_roots hq0, IsRoot, hqdef, eval_map_algebraMap] at hz; exact hz
    obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hz'
    have h1 : finEmb F v τ ((1 : v.adicCompletion F) ⊗ₜ[F] x) = z := by rw [finEmb_tmul, map_one, one_mul, hτ]
    show absBar F v z ≤ M
    rw [← h1]; exact (le_absFin F v τ _).trans (le_max_right _ _)
  have hcard : Multiset.card q.roots ≤ Module.finrank F E := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdef, natDegree_map]; exact minpoly.natDegree_le x
  have key := val_coeff_prod_X_sub_C_le (valBar F v) hM q.roots hroots j
  rw [← hq] at key
  have hc : valBar F v (q.coeff j) = ‖algebraMap F (v.adicCompletion F) (p.coeff j)‖₊ := by
    show absBar F v _ = _
    rw [hqdef, coeff_map, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (FvBar F v), absBar_algebraMap]
  rw [← hc]
  exact key.trans (pow_le_pow_right₀ hM hcard)

end GlobalTheory.CoefHeight
end

section

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory

theorem minpoly_coeff_le_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (w : InfinitePlace F) (j : ℕ) :
    w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E *
      ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  set M : ℝ≥0 := max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) with hM
  set p := minpoly F x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h1 : p.Monic := minpoly.monic hx
  have hd : p.natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
  have h3 : ∀ z ∈ (p.map w.embedding).roots, ‖z‖ ≤ (M : ℝ) := by
    intro z hz
    have hz' : z ∈ p.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨h1.ne_zero, ?_⟩
      have := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero h1)).1 hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact this
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
    obtain ⟨ψ, rfl⟩ := hz'
    let τ : EmbOver E w := ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
    have : ‖ψ x‖₊ ≤ M :=
      le_trans (Finset.le_sup (f := fun τ : EmbOver E w => ‖τ.1 x‖₊) (Finset.mem_univ τ)) (le_max_right _ _)
    exact_mod_cast this
  have key := Polynomial.coeff_le_of_roots_le (f := w.embedding) j h1 (IsAlgClosed.splits _) h3
  rw [Polynomial.coeff_map] at key
  have hw : w (p.coeff j) = ‖w.embedding (p.coeff j)‖ := (InfinitePlace.norm_embedding_eq w _).symm
  rw [hw]
  refine key.trans ?_
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
  have hpow : (M : ℝ) ^ (p.natDegree - j) ≤ (M : ℝ) ^ Module.finrank F E :=
    pow_le_pow_right₀ hM1 (le_trans (Nat.sub_le _ _) hd)
  have hch : ((p.natDegree.choose j : ℕ) : ℝ) ≤ 2 ^ Module.finrank F E := by
    have := (Nat.choose_le_two_pow p.natDegree j).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact_mod_cast this
  rw [mul_comm]
  exact mul_le_mul hch hpow (by positivity) (by positivity)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormInf

theorem infPlace_norm_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (y : E) (c : ℝ≥0) (h : ∀ τ : GlobalTheory.AdelicU.EmbOver E w, ‖τ.1 y‖₊ ≤ c) :
    w (Algebra.norm F y) ≤ (c : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  rw [← InfinitePlace.norm_embedding_eq]
  have e : w.embedding (Algebra.norm F y) = ∏ σ : E →ₐ[F] ℂ, σ y := Algebra.norm_eq_prod_embeddings F ℂ y
  rw [e, norm_prod, ← AlgHom.card F E ℂ]
  calc ∏ σ : E →ₐ[F] ℂ, ‖σ y‖ ≤ ∏ _σ : E →ₐ[F] ℂ, (c : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun σ _ => by
          exact_mod_cast h ⟨σ.toRingHom, RingHom.ext σ.commutes⟩
    _ = (c : ℝ) ^ Fintype.card (E →ₐ[F] ℂ) := by rw [Finset.prod_const, Finset.card_univ]

theorem main : ∀ (D : D7) (w : InfinitePlace D.host.F) (y : D.host.E) (c : ℝ≥0), (∀ τ : GlobalTheory.AdelicU.EmbOver D.host.E w, ‖τ.1 y‖₊ ≤ c) → w (Algebra.norm D.host.F y) ≤ (c : ℝ) ^ Module.finrank D.host.F D.host.E :=
  fun D w y c h => infPlace_norm_le w y c h

end GlobalTheory.NormInf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormFin
open GlobalTheory.AdelicU

theorem nnnorm_algebraMap_norm_le (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    ‖algebraMap F (Fv F v) (Algebra.norm F y)‖₊ ≤
      absFin F v ((1 : Fv F v) ⊗ₜ[F] y) ^ Module.finrank F E := by
  rw [← absBar_algebraMap F v, ← IsScalarTower.algebraMap_apply,
    Algebra.norm_eq_prod_embeddings F (FvBar F v) y]
  rw [show absBar F v (∏ τ : E →ₐ[F] FvBar F v, τ y) = ∏ τ : E →ₐ[F] FvBar F v, absBar F v (τ y) from
    map_prod (valBar F v) _ _]
  rw [← AlgHom.card F E (FvBar F v), ← Finset.card_univ]
  refine Finset.prod_le_pow_card _ _ _ fun τ _ => ?_
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] y)
  simpa using this

theorem normFin_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E) :
    ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤
      GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E :=
  nnnorm_algebraMap_norm_le D.host.F v y

end GlobalTheory.NormFin
end
end

section

noncomputable section

namespace GlobalTheory.RatCount

open NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped TensorProduct
open scoped NNReal

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]


open Classical in
def htE (x : E) : ℝ≥0 :=
  (∏ w : InfinitePlace F, max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x))

end GlobalTheory.RatCount
end
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.card_minus_signs_half_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.m → 0 < G.ga → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧ (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 := by
  first | exact @GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | exact GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | (intros; apply GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters <;> assumption)
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.harish_chandra_param_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  first | exact @GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | exact GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | (intros; apply GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 <;> assumption)
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.parameters_separated_by_one : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  first | exact @GlobalTheory.WordSep.word_sep | exact GlobalTheory.WordSep.word_sep | (intros; apply GlobalTheory.WordSep.word_sep <;> assumption)
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.signed_parameters_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 → ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  first | exact @GlobalTheory.Twist.parPi_parD0_entries_bounded | exact GlobalTheory.Twist.parPi_parD0_entries_bounded | (intros; apply GlobalTheory.Twist.parPi_parD0_entries_bounded <;> assumption)
end
