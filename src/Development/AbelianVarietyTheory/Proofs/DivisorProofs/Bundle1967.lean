module

public import Aesop.BuiltinRules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateCmValueCharacterPermutedWeight
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem norm_addChar_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y : k, ‖ψ y‖ ≤ 1 := by
    intro y
    have hK : IsCompact ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).image (by fun_prop)
    obtain ⟨C, hC⟩ := (hK.image (continuous_norm.comp hψ)).isBounded.exists_norm_le
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    have hmem : ‖ψ (y * (n : k))‖ ∈ (fun z => ‖ψ z‖) '' ((fun u : k => y * u) '' (𝒪[k] : Set k)) :=
      ⟨y * n, ⟨n, natCast_mem _ n, rfl⟩, rfl⟩
    have h2 := hC _ hmem
    rw [Real.norm_of_nonneg (norm_nonneg _), mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at h2
    linarith
  have h1 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, h1, norm_one]
  have a := hle x
  have b := hle (-x)
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

def toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) : AddChar k Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_addChar_eq_one ψ hψ x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (by show ψ (a + b) = ψ a * ψ b; exact AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k ℂ) (hψ : Continuous ψ) (x : k) : (toCircle ψ hψ x : ℂ) = ψ x := rfl

def colH (k : Type) [TopologicalSpace k] (κ : Type) : (κ → k) ≃ₜ Matrix κ Unit k where
  toFun x := Matrix.of fun i _ => x i
  invFun M i := M i ()
  left_inv _ := rfl
  right_inv M := by ext i j; cases j; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun _ => continuous_apply i
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    exact (continuous_apply () ).comp (continuous_apply i)

theorem sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) {f : Y → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB Y) : f ∘ h ∈ GlobalTheory.WeilM.SB X :=
  ⟨hf.1.comp_continuous h.continuous, hf.2.comp_homeomorph h⟩

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

open ValuativeRel

theorem schr_irreducible_local (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (N : Submodule ℂ ((κ → k) → ℂ)) (hN : N ≤ GlobalTheory.WeilM.SB (κ → k))
    (hS : ∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) (φ₀ : (κ → k) → ℂ) (h0 : φ₀ ∈ N) (hne : φ₀ ≠ 0) :
    N = GlobalTheory.WeilM.SB (κ → k) := by
  classical
  let e := colH k κ
  let L : (Matrix κ Unit k → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) := LinearMap.funLeft ℂ ℂ e
  have hL : ∀ Φ, L Φ = Φ ∘ e := fun _ => rfl
  have hcirc : Continuous (toCircle ψk hc) := by
    have : Continuous (fun x => ((toCircle ψk hc x : Circle) : ℂ)) := hc
    exact continuous_induced_rng.2 this
  have hne1 : toCircle ψk hc ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [coe_toCircle] using this
  have hW : N.comap L ≤ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) := by
    intro Φ hΦ
    have h := sb_comp e.symm (hN hΦ)
    have : (Φ ∘ e) ∘ e.symm = Φ := by funext M; simp
    rw [← this]
    exact h
  have hT : ∀ Φ ∈ N.comap L, ∀ x : Matrix κ Unit k, (fun t => Φ (t + x)) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => Φ (t + x)) ∈ N.comap L := by
    intro Φ hΦ x _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (e.symm x, 0) _ hΦ
    convert h using 1
    funext y
    have he : e (y + e.symm x) = e y + x := by ext i j; cases j; rfl
    simp [schr, he]
  have hM : ∀ Φ ∈ N.comap L, ∀ b : Matrix κ Unit k,
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ GlobalTheory.SplitWeil.SB (Matrix κ Unit k) →
      (fun t => ((toCircle ψk hc (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) * Φ t) ∈ N.comap L := by
    intro Φ hΦ b _
    rw [Submodule.mem_comap, hL] at hΦ ⊢
    have h := hS (0, fun r => b r ()) _ hΦ
    convert h using 1
    funext y
    simp [schr, dotProduct, coe_toCircle, e, colH, mul_comm]
    change Φ (e y) * ψk (∑ r, b r () * y r) = ψk (∑ r, b r () * y r) * Φ (e y)
    exact mul_comm _ _
  have h0' : φ₀ ∘ e.symm ∈ N.comap L := by
    rw [Submodule.mem_comap, hL]
    have : (φ₀ ∘ e.symm) ∘ e = φ₀ := by funext y; simp
    rw [this]; exact h0
  have hne' : φ₀ ∘ e.symm ≠ 0 := by
    intro h
    apply hne
    funext y
    have := congrFun h (e y)
    simpa using this
  have hall := GlobalTheory.IrredSB.sb_irreducible k κ Unit (toCircle ψk hc) hcirc hne1 (N.comap L) hW hT hM _ h0' hne'
  refine le_antisymm hN fun φ hφ => ?_
  have hm : φ ∘ e.symm ∈ N.comap L := by
    rw [hall]
    exact sb_comp e.symm hφ
  rw [Submodule.mem_comap, hL] at hm
  have : (φ ∘ e.symm) ∘ e = φ := by funext y; simp
  rwa [this] at hm

end GlobalTheory.SchrIrred

namespace GlobalTheory.SchrIrred

theorem schr_irreducible : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ N : Submodule ℂ ((κ → Fv F v) → ℂ), N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) → (∀ w, ∀ φ ∈ N, schr ψk w φ ∈ N) → ∀ φ₀ ∈ N, φ₀ ≠ 0 →
      N = GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v κ _ ψk hc h1 N hN hS φ₀ h0 hne
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  exact schr_irreducible_local (Fv F v) ψk hc h1 N hN hS φ₀ h0 hne

end GlobalTheory.SchrIrred
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  first | (exact @GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (exact GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (intros; apply GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton  <;> assumption)
end

section

open NumberField GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.exists_conjugate_cmValueCharacter_permuted_weight : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φK : K →+* ℂ) (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E) (σ : ℂ ≃+* ℂ), IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = φK) → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → IsValChar φ s κ 𝔣 ∅ χ → ∃ (π : Equiv.Perm I) (χ' : HChar E), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjWt φ σ κ (κ ∘ π) ∧ GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsConjChar φ s (κ ∘ π) σ χ χ' ∧ IsValChar φ s (κ ∘ π) 𝔣 ∅ χ' := by
  first | exact @GlobalTheory.ConjValChar.exists_conj_valChar | exact GlobalTheory.ConjValChar.exists_conj_valChar | (intros; apply GlobalTheory.ConjValChar.exists_conj_valChar <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC

section Arith

variable {D : D7}

theorem rankV_lt_gap {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) : rankV D (i + 1) (j + 1) < gap D 1 := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    unfold rankV bigN
    rw [mul_add, mul_add, mul_one]
    omega
  have h4 := (isLeast_gap D 1).1.2.1
  have h5 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem numE_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    0 ≤ (num D 1 τ).e (j + 1) ∧ ((num D 1 τ).e (j + 1) : ℝ) ≤ 4 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := hs
  have e1 : (D.hc τ).e ⟨j, hj⟩ = ((num D 1 τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 ⟨j, hj⟩
  obtain ⟨hb0, he4⟩ := hbe τ ⟨j, hj⟩
  have hg := (D.hc τ).gap_be ⟨j, hj⟩
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [e1] at hg he4
  refine ⟨?_, by exact_mod_cast he4⟩
  have : (0 : ℚ) ≤ ((num D 1 τ).e (j + 1) : ℚ) := by linarith
  exact_mod_cast this

theorem cen_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) : 0 ≤ cen D 1 τ i ∧ (cen D 1 τ i : ℝ) ≤ L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  set G0 := GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have ev : (D.hc τ).v ⟨0, by omega⟩ = (G0.v 2 : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, by omega⟩
  obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨0, by omega⟩
  rw [ev] at v0 v1
  have hmid : G0.mid i = (G0.v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) + (gap D 1 : ℚ) / 2 :=
    G0.mid_eq h1
  have hc : cen D 1 τ i = ⌊G0.mid i⌋ := rfl
  have hS := L.Sc_pos
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hi2 : (i : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have hγ : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : ((G0.mid i : ℚ) : ℝ) = (G0.v 2 : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 := by
    rw [hmid]; push_cast; ring
  have v0' : (0 : ℝ) ≤ (G0.v 2 : ℝ) := by exact_mod_cast v0
  have v1' : (G0.v 2 : ℝ) ≤ L.Sc := by exact_mod_cast v1
  have m0 : (0 : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by
    rw [hmR]; have : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ
    linarith
  have m1 : ((G0.mid i : ℚ) : ℝ) ≤ L.sc.b := by
    rw [hmR]
    have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    linarith
  have m0q : (0 : ℚ) ≤ G0.mid i := by exact_mod_cast m0
  refine ⟨hc ▸ Int.floor_nonneg.2 m0q, ?_⟩
  have hf : ((⌊G0.mid i⌋ : ℚ) : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by exact_mod_cast Int.floor_le (G0.mid i)
  rw [hc]
  push_cast at hf ⊢
  linarith

theorem gap_le_b {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) : (gap D 1 : ℝ) ≤ L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨-, -, -, hm, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hS := L.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have h15 : 15 ≤ gap D 1 := by have : 6 ≤ sLen D := by unfold sLen; omega
                                omega
  have hγ : (15 : ℝ) ≤ gap D 1 := by exact_mod_cast h15
  have hm' : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  constructor <;> nlinarith

theorem maxWt_le {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) :
    1 ≤ (maxWt D 1 : ℝ) ∧ (maxWt D 1 : ℝ) ≤ 10 * L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨hγb, hb⟩ := gap_le_b hs
  have key : ∀ x : Fin D.R.m × Fin D.R.m × D.what₂.Tau,
      max (wtA D 1 x.1 x.2.1 x.2.2).natAbs (wtA' D 1 x.1 x.2.1 x.2.2).natAbs ≤ ⌊10 * L.sc.b⌋₊ := by
    rintro ⟨i, j, τ⟩
    have hr := rankV_lt_gap (D := D) i.2 j.2
    have hij : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have hbs : botSmall D i j ≤ rankV D (i + 1) (j + 1) := by unfold botSmall; omega
    have hbb : botBig D i j ≤ rankV D (i + 1) (j + 1) := by unfold botBig; omega
    have hp : rankV D i j % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    obtain ⟨e0, e1⟩ := numE_bounds hs τ j.2
    obtain ⟨c0, c1⟩ := cen_bounds hs τ (i := D.R.m - i) (by omega) (by omega)
    dsimp only
    refine max_le (Nat.le_floor ?_) (Nat.le_floor ?_)
    · have hA : |wtA D 1 i j τ| ≤ 2 * (num D 1 τ).e (j + 1) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA
        constructor <;> omega
      have hA' : |((wtA D 1 i j τ : ℤ) : ℝ)| ≤ 2 * ((num D 1 τ).e (j + 1) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    · have hA : |wtA' D 1 i j τ| ≤ 2 * cen D 1 τ (D.R.m - i) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA'
        constructor <;> omega
      have hA' : |((wtA' D 1 i j τ : ℤ) : ℝ)| ≤ 2 * (cen D 1 τ (D.R.m - i) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
  have hsup : maxWt D 1 ≤ max 1 ⌊10 * L.sc.b⌋₊ := max_le_max le_rfl (Finset.sup_le fun x _ => key x)
  have hfl : (⌊10 * L.sc.b⌋₊ : ℝ) ≤ 10 * L.sc.b := Nat.floor_le (by linarith)
  refine ⟨by exact_mod_cast le_max_left 1 _, ?_, hb⟩
  have : (maxWt D 1 : ℝ) ≤ ((max 1 ⌊10 * L.sc.b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
  rw [Nat.cast_max, Nat.cast_one] at this
  exact this.trans (max_le (by linarith) hfl)

end Arith

end GlobalTheory.BigTop.Fun

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt | exact GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt | (intros; apply GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.eventually_integralPointsIndicator_isVacuum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ᶠ v in Filter.cofinite, M.IsVac B.ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  first | exact @GlobalTheory.StdVacuum.eventually_isVac_indicator | exact GlobalTheory.StdVacuum.eventually_isVac_indicator | (intros; apply GlobalTheory.StdVacuum.eventually_isVac_indicator <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdeleUnitModule

open scoped Pointwise ENNReal

theorem map_smul_eq_inv_smul {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun x => g • x) = ((distribHaarChar A g : ℝ≥0∞))⁻¹ • μ := by
  have h1 : DomMulAct.mk g⁻¹ • μ = μ.map (fun x => g • x) := by
    ext s hs
    rw [Measure.domSMul_apply, Measure.map_apply (measurable_const_smul g) hs, Set.preimage_smul]
    simp
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk g⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ g⁻¹, map_inv (distribHaarChar A)] at h2
  rw [← h1, h2, ENNReal.smul_def, ENNReal.coe_inv (distribHaarChar_pos).ne']

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

theorem distribHaarChar_eq_absE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [SecondCountableTopology (AE F E)] [T2Space (AE F E)]
    (t : (AE F E)ˣ) : distribHaarChar (AE F E) t = absE F E t := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  let φ : AE F E ≃ₜ+ AdeleRing (𝓞 E) E :=
    { (adeleTensorAlgEquivLeft F E).toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap }
  haveI : SecondCountableTopology (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.isEmbedding.t2Space
  have h1 : distribHaarChar (AdeleRing (𝓞 E) E) (GlobalTheory.IdeleLogHom.toE F E t) = distribHaarChar (AE F E) t :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport φ t (GlobalTheory.IdeleLogHom.toE F E t) (fun x => by
      change adeleTensorAlgEquivLeft F E ((t : AE F E) * x) = _
      rw [map_mul]
      rfl)
  apply NNReal.eq
  rw [← h1, GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.IdeleLogHom.absE_eq_ideleModule]

theorem map_mul_eq_absE_inv_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AE F E)] [BorelSpace (AE F E)] (ν : Measure (AE F E)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun x => (t : AE F E) * x) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ _ _ ν _ t
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have h := map_smul_eq_inv_smul ν t
  rw [distribHaarChar_eq_absE] at h
  exact h

end GlobalTheory.AdeleUnitModule
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_lattice_character_trivial : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  first | exact @GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt | exact GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt | (intros; apply GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (r s : ℕ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    HasSig M r s → HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSig.hasSig_complement_plane | exact GlobalTheory.PlaneSig.hasSig_complement_plane | (intros; apply GlobalTheory.PlaneSig.hasSig_complement_plane <;> assumption)
end
