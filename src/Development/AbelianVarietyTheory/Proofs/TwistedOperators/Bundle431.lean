module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle397
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section
namespace GlobalTheory.FlipMatch.FieldTransport
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace
open ValuativeRel

section
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {n : Type} [Fintype n] [DecidableEq n]


omit [IsNonarchimedeanLocalField k] [IsNonarchimedeanLocalField k'] in
theorem val_le_iff (hj : IsLocIso j) (x y : k) :
    valuation k' (j x) ≤ valuation k' (j y) ↔ valuation k x ≤ valuation k y := by
  by_cases hy : y = 0
  · subst hy; simp
  have h := hj.2.2 (x / y)
  have h0 : 0 < valuation k y := zero_lt_iff.2 (by simpa using hy)
  have h1 : 0 < valuation k' (j y) := zero_lt_iff.2 (by simpa using hy)
  rwa [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_div₀, map_div₀, map_div₀, div_le_one₀ h0,
    div_le_one₀ h1] at h

theorem isUnif_map (hj : IsLocIso j) {ϖ : kˣ} (h : IsUnif ϖ) : IsUnif (Units.map (j : k →* k') ϖ) := by
  have hlt : ∀ x, valuation k' (j x) < 1 ↔ valuation k x < 1 := fun x => by
    have := (val_le_iff hj 1 x).not
    simpa only [map_one, not_le] using this
  obtain ⟨ϖ', h'⟩ := exists_isUnif (k := k')
  show valuation k' (j ϖ) = uniformizer k'
  refine le_antisymm (le_uniformizer_iff.2 ((hlt _).2 (h ▸ uniformizer_lt_one))) ?_
  obtain ⟨y, hy⟩ := j.surjective ϖ'
  rw [← show valuation k' (ϖ' : k') = uniformizer k' from h', ← hy, val_le_iff hj,
    show valuation k (ϖ : k) = uniformizer k from h, le_uniformizer_iff, ← hlt, hy]
  exact h' ▸ uniformizer_lt_one

theorem shellSet_subset {ϖ ϖ' : kˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    shellSet ϖ m ⊆ shellSet ϖ' m := by
  intro g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  have hu : ∀ r : ℤ, valuation k (((ϖ / ϖ') ^ r : kˣ) : k) = 1 := fun r => by
    have h1 : valuation k ((ϖ : k) / ϖ') = 1 := by
      rw [map_div₀, show valuation k (ϖ : k) = _ from h, show valuation k (ϖ' : k) = _ from h']
      exact div_self uniformizer_ne_zero
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_div_eq_div_val, h1, _root_.one_zpow]
  have hd : ∀ c : n → kˣ, (∀ i, valuation k (c i : k) = 1) → ∀ i l, (diagGL c).val i l ∈ 𝒪[k] := fun c hc i l => by
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc i).le
    · exact zero_mem _
  have hK : (diagGL fun i => (ϖ / ϖ') ^ m i) ∈ KO k n := (mem_KO_iff _).2 ⟨hd _ fun i => hu _,
    hd (fun i => ((ϖ / ϖ') ^ m i)⁻¹) fun i => by rw [← _root_.zpow_neg]; exact hu _⟩
  refine mem_shellSet.2 ⟨_, mul_mem hx hK, y, hy, ?_⟩
  congr 1
  rw [mul_assoc]
  congr 1
  have := diagHom.map_mul (fun i => (ϖ / ϖ') ^ m i) (fun i => ϖ' ^ m i)
  refine Eq.trans ?_ this
  show SplitFlip.diagGL _ = SplitFlip.diagGL _
  congr 1
  funext i
  simp [← mul_zpow]

def glEquiv (j : k ≃+* k') (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL n k' :=
  Units.mapEquiv (j.mapMatrix (m := n)).toMulEquiv


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in
theorem glEquiv_val (g : GL n k) : (glEquiv j n g).val = g.val.map j := rfl


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] in
theorem gdet_glEquiv (g : GL n k) : gdet (glEquiv j n g) = Units.map (j : k →* k') (gdet g) :=
  Units.ext ((j : k →+* k').map_det g.val).symm

def glHomeo (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ₜ* GL n k' :=
  { glEquiv j n with
    continuous_toFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.1)
    continuous_invFun := isEmbedding_val_GL.continuous_iff.2 (Units.continuous_val.matrix_map hj.2.1) }

theorem glEquiv_mem_KO (hj : IsLocIso j) (g : GL n k) : glEquiv j n g ∈ KO k' n ↔ g ∈ KO k n := by
  rw [mem_KO_iff, mem_KO_iff, ← map_inv]
  simp only [glEquiv_val, map_apply, hj.2.2]

theorem preimage_shellSet (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ') (m : n → ℤ) :
    glEquiv j n ⁻¹' shellSet ϖ' m = shellSet ϖ m := by
  rw [(shellSet_subset h' (isUnif_map hj h) m).antisymm (shellSet_subset (isUnif_map hj h) h' m)]
  have hd : glEquiv j n (diagGL fun i => ϖ ^ m i) = diagGL fun i => (Units.map (j : k →* k') ϖ) ^ m i :=
    Units.ext (by rw [glEquiv_val, diagGL_val, diagGL_val, diagonal_map (map_zero _)]; simp)
  ext g
  rw [Set.mem_preimage, mem_shellSet, mem_shellSet, ← hd]
  constructor
  · rintro ⟨x, hx, y, hy, H⟩
    obtain ⟨x, rfl⟩ := (glEquiv j n).surjective x
    obtain ⟨y, rfl⟩ := (glEquiv j n).surjective y
    rw [← map_mul, ← map_mul] at H
    exact ⟨x, (glEquiv_mem_KO hj _).1 hx, y, (glEquiv_mem_KO hj _).1 hy, (glEquiv j n).injective H⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, (glEquiv_mem_KO hj _).2 hx, _, (glEquiv_mem_KO hj _).2 hy, by rw [map_mul, map_mul]⟩

theorem apow_map (hj : IsLocIso j) (x : kˣ) (z : ℂ) : apow (Units.map (j : k →* k') x) z = apow x z := by
  have := GlobalTheory.SplitWeil.nabs_map_of_homeomorph j hj.1 hj.2.1 x
  unfold apow
  congr 2

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

def glMeas (hj : IsLocIso j) (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃ᵐ GL n k' :=
  (glHomeo hj n).toHomeomorph.toMeasurableEquiv

theorem isHaar_map (hj : IsLocIso j) (μ : Measure (GL n k)) [μ.IsHaarMeasure] : (μ.map (glMeas hj n)).IsHaarMeasure :=
  (glHomeo hj n).isHaarMeasure_map μ

theorem map_haarVol (hj : IsLocIso j) : (haarVol (KO k n)).map (glMeas hj n) = haarVol (KO k' n) := by
  have := isHaar_map hj (haarVol (KO k n))
  refine eq_haarVol _ isOpen_KO le_rfl ?_
  rw [MeasurableEquiv.map_apply, show glMeas hj n ⁻¹' (KO k' n : Set (GL n k')) = KO k n from
    Set.ext fun g => glEquiv_mem_KO hj g]
  exact haarVol_self isOpen_KO le_rfl

variable {C : Type} [Fintype C] [DecidableEq C] {ν : kˣ →* ℂˣ} {ν' : k'ˣ →* ℂˣ}

theorem shell_map (hj : IsLocIso j) {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (z : ℂ) (φ : Matrix n n k' → ℂ) (m : n → ℤ) :
    shell (haarVol (KO k n)) ϖ ν z (fun X => φ (X.map j)) m = shell (haarVol (KO k' n)) ϖ' ν' z φ m := by
  unfold shell
  rw [← map_haarVol hj, setIntegral_map_equiv, ← preimage_shellSet hj h h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = φ (glEquiv j _ g).val * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val]


omit [DecidableEq C] in
theorem bigF_map (hj : IsLocIso j) {a : ℕ} {ϖ : kˣ} {ϖ' : k'ˣ} (h : IsUnif ϖ) (h' : IsUnif ϖ')
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ξ : Matrix (Fin a) C k' → ℂ) (X : Matrix (Fin a) C k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun X => Ξ (X.map j)) X = bigF (haarVol (KO k' (Fin a))) ϖ' ν' Ξ (X.map j) := by
  unfold bigF shellSum
  refine finsum_congr fun m => ?_
  rw [← shell_map hj h h' hν]
  simp only [Matrix.map_mul]


omit [DecidableEq C] in
theorem smallF_map (hj : IsLocIso j) (μ : Measure (GL n k))
    (hν : ∀ x, ν x = ν' (Units.map (j : k →* k') x)) (Ψ : Matrix n C k' → ℂ) (Y : Matrix n C k) :
    smallF μ ν (fun Y => Ψ (Y.map j)) Y = smallF (μ.map (glMeas hj n)) ν' Ψ (Y.map j) := by
  unfold smallF
  rw [integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ = Ψ ((glEquiv j _ g).val * Y.map j) * ν' (gdet (glEquiv j _ g)) * apow (gdet (glEquiv j _ g)) _
  rw [gdet_glEquiv, apow_map hj, ← hν, glEquiv_val, ← Matrix.map_mul]

end

theorem zeta_identity_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (k' : Type) [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [MeasurableSpace k'] [BorelSpace k'] (j : k ≃+* k'), IsLocIso j → ∀ (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C] (σ : Fin a ⊕ A' ≃ C)
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k')) [μ'.IsHaarMeasure] (ϖ : kˣ) (ϖ' : k'ˣ), IsUnif ϖ → IsUnif ϖ' →
    ∀ (ν β : kˣ →* ℂˣ) (ν' β' : k'ˣ →* ℂˣ), (∀ x, ν x = ν' (Units.map (j : k →* k') x)) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a) C k' → ℂ) (Ψ : Matrix A' C k' → ℂ),
      bigP (haarVol (KO k' (Fin a))) ϖ' σ ν' β' Ξ = smallP μ' σ ν' (ν' * β') Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (X.map j)) = smallP μ σ ν (ν * β) fun Y => lam * Ψ (Y.map j) := by
  intro k _ _ _ _ _ _ k' _ _ _ _ _ _ j hj a A' _ _ C _ _ σ μ _ μ' _ ϖ ϖ' h h' ν β ν' β' hν
  have := isHaar_map hj μ
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (glMeas hj A')) μ'
  have hc0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map (glMeas hj A')) μ').ne'
  generalize Measure.haarScalarFactor (μ.map (glMeas hj A')) μ' = c at hc hc0
  have hc1 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨((c : ℝ) : ℂ)⁻¹, inv_ne_zero hc1, fun Ξ Ψ H => funext fun g => ?_⟩
  have H1 := congrFun H (glEquiv j C g)
  have hX : (X0 k σ * (invT g).val).map j = X0 k' σ * (invT (glEquiv j C g)).val := by
    ext i l
    rw [map_apply, frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply]; rfl
  have hY : (Y0 k σ * g.val).map j = Y0 k' σ * (glEquiv j C g).val := by
    ext i l
    rw [map_apply, frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]; rfl
  have hS : smallF μ ν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ (Y.map j)) (Y0 k σ * g.val) =
      smallF μ' ν' Ψ (Y0 k' σ * (glEquiv j C g).val) := by
    rw [smallF_map hj μ hν (fun Y => ((c : ℝ) : ℂ)⁻¹ * Ψ Y), hc, hY]
    simp only [smallF, integral_smul_nnreal_measure, mul_assoc, integral_const_mul, NNReal.smul_def,
      Complex.real_smul]
    rw [inv_mul_cancel_left₀ hc1]
  rw [bigZetaIntegral_eq, smallP, gdet_glEquiv, apow_map hj, apow_map hj, MonoidHom.mul_apply, ← hν, Units.val_mul] at H1
  rw [bigZetaIntegral_eq, smallP, bigF_map hj h h' hν, hS, hX, MonoidHom.mul_apply, Units.val_mul]
  have hb : ((β' (Units.map (j : k →* k') (gdet g)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  apply mul_left_cancel₀ hb
  linear_combination (β (gdet g) : ℂ) * H1

end GlobalTheory.FlipMatch.FieldTransport
end
end

section

namespace GlobalTheory.ColFourier
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat
attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_const T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.ColFourier.fourierInt_eq_fourierSum k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

theorem _root_.GlobalTheory.T.exists_rationalUnitary_scaling_wittFrame : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)), ∃ g : GF V, (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x) ∧ (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E)⁻¹ • x) ∧ ∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z := by
  first | exact @GlobalTheory.TrScale.exists_scale | exact GlobalTheory.TrScale.exists_scale | (intros; apply GlobalTheory.TrScale.exists_scale <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

theorem _root_.GlobalTheory.T.commute_of_wittFrame_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  first | exact @GlobalTheory.Cusp.WeightCommute.commute_of_weights | exact GlobalTheory.Cusp.WeightCommute.commute_of_weights | (intros; apply GlobalTheory.Cusp.WeightCommute.commute_of_weights <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

theorem _root_.GlobalTheory.T.exists_pow_archProj_not_mem_of_eigenvalue_two : ∀ (D : D7) (V : HSp D) (g : GF V) (x : V.V), x ≠ 0 → GlobalTheory.Cusp.ratAct D.sp.cm V g x = (2 : D.host.E) • x → ∀ (w : InfinitePlace D.host.F) (K : Set (GArch D.sp.cm.sig V.gram w)), IsCompact K → ∃ n : ℕ, projArch D.sp.cm.sig V.gram w (rat V (g ^ n)) ∉ K := by
  first | exact @GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two | exact GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two | (intros; apply GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

def complId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (AE D) :=
  AddSubgroup.closure {s | ∃ α ∈ intAf D.host.F, ∃ a ∈ 𝔠, s = pairA D.host.F 0 α ⊗ₜ[D.host.F] a}

theorem tmul_mem_complId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {a : D.host.E} (ha : a ∈ 𝔠) : pairA D.host.F 0 α ⊗ₜ[D.host.F] a ∈ complId 𝔠 :=
  AddSubgroup.subset_closure ⟨α, hα, a, ha, rfl⟩

end GlobalTheory.XCharBF

end
end
