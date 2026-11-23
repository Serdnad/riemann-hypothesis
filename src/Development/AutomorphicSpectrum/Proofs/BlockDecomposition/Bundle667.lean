module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle658
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle004
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InducedVanishOfVanishOnIntegral
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle006
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle005
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
import Formalism.DoubleCosetMeasures.Statement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.AutomorphicForms.Bundle009
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem mul_frameLine {n r : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    (Q : Matrix (Fin r) (Fin n) ℂ) {d : Fin r → ℂ} (hA : A * P = P * diagonal d) (i : Fin r) :
    A * (P * single i i (1 : ℂ) * Q) = d i • (P * single i i (1 : ℂ) * Q) := by
  have e : diagonal d * single i i (1 : ℂ) = d i • single i i (1 : ℂ) := by
    ext a b
    by_cases h : i = a
    · subst h
      simp [Matrix.diagonal_mul, Matrix.single_apply]
    · simp [Matrix.diagonal_mul, Matrix.single_apply, h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.mul_assoc P, e, Matrix.mul_smul, Matrix.smul_mul]

theorem map_frameLine {E : Type} [Field E] {n r : ℕ} (f : E →+* ℂ) (P : Matrix (Fin n) (Fin r) E)
    (Q : Matrix (Fin r) (Fin n) E) (i : Fin r) :
    (P * single i i (1 : E) * Q).map f = P.map f * single i i (1 : ℂ) * Q.map f := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  by_cases h : a = i ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [Matrix.single_apply, show ¬(i = a ∧ i = b) from fun q => h ⟨q.1.symm, q.2.symm⟩]

theorem torus_mul_frameIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → (∀ i, 0 < t i) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (β : FrameIx r), archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = ((frameWt t β : ℝ) : ℂ) • (frameIdem (σ : E →+* E) J X Y β).map τ.1 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW t a ha _ w τ β
  obtain ⟨h1, h2, h3⟩ := ha.2 w τ
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => sigma_sigma h _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  rcases β with _ | i | i
  · have hV : (cT (σ : E →+* E) X * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
      simp
    have hU : (cT (σ : E →+* E) Y * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx]
      simp
    have col : ∀ (M : Matrix (Fin r) (Fin n) E), M * frameIdem (σ : E →+* E) J X Y none = 0 → ∀ j,
        M *ᵥ (fun k => frameIdem (σ : E →+* E) J X Y none k j) = 0 := fun M hM j => by
      funext i
      exact congrFun (congrFun hM i) j
    have key : archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y none).map τ.1 =
        (frameIdem (σ : E →+* E) J X Y none).map τ.1 := by
      ext i j
      exact congrFun (h3 _ (col _ hV j) (col _ hU j)) i
    simpa [frameWt] using key
  · simp only [frameIdem, frameWt]
    rw [map_frameLine]
    exact mul_frameLine _ h1 i
  · simp only [frameIdem, frameWt]
    rw [map_frameLine, Complex.ofReal_inv]
    exact mul_frameLine _ h2 i

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitNarrow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK.SplitAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_condLE {ϖ : kˣ} {e : ℕ} {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : IsSmoothChar χ := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h1 : IsOpen (({x : kˣ | (x : k) ∈ (𝒪[k] : Set k)} ∩ {x : kˣ | ((x⁻¹ : kˣ) : k) ∈ (𝒪[k] : Set k)}) ∩
      {x : kˣ | ((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹ ∈ (𝒪[k] : Set k)}) :=
    ((ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)).inter
      (ho.preimage ((Units.continuous_val.sub continuous_const).mul continuous_const))
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (h1.mem_nhds ?_) ?_)
  · refine ⟨⟨one_mem 𝒪[k], by simpa using one_mem 𝒪[k]⟩, ?_⟩
    simpa using zero_mem 𝒪[k]
  · rintro x ⟨⟨hx, hx'⟩, hx''⟩
    have a1 : valuation k (x : k) ≤ 1 := hx
    have a2 : valuation k ((x⁻¹ : kˣ) : k) ≤ 1 := hx'
    have a3 : valuation k (((x : k) - 1) * (((ϖ ^ e : kˣ) : k))⁻¹) ≤ 1 := hx''
    have hc : valuation k (((ϖ ^ e : kˣ) : k)) ≠ 0 := by simp
    refine h x ⟨le_antisymm a1 ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
      exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 a2
    · rw [map_mul, map_inv₀] at a3
      have a4 := (mul_inv_le_iff₀ (zero_lt_iff.2 hc)).1 a3
      rwa [one_mul] at a4

def IndIrredNarrow : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    a' < a → ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredNarrow_of
    (NB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) : IndIrredNarrow := by
  intro k _ _ _ _ a a' α β sα sβ hα hβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

theorem irred_of_setting (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    (N : Submodule ℂ (GL (Fin (a + a')) k → ℂ)) (hN : N ≤ indSp a a' α β) (hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) :
    N = ⊥ ∨ N = indSp a a' α β := by
  obtain ⟨e, h1, h2⟩ := H.cond
  exact hI k a a' α β (isSmoothChar_of_condLE h1) (isSmoothChar_of_condLE h2) H.unitα H.unitβ H.lt N hN hst

theorem onto_of_irred (hI : IndIrredNarrow) {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ} (H : HidaSetting a a' ϖ α β ν)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hadd : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁) (hmem : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ)) (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) :
    ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + Φ₁, add_mem hΦ hΦ₁, by simpa using hadd Φ hΦ Φ₁ hΦ₁ 1⟩
      zero_mem' := ⟨0, zero_mem _, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨c • Φ, (SB X).smul_mem c hΦ, by simpa [h0] using hadd 0 (zero_mem _) Φ hΦ c⟩ }
  rcases irred_of_setting hI H N (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hmem Φ hΦ)
    (by rintro h₁ _ ⟨Φ, hΦ, rfl⟩; exact heq Φ hΦ h₁) with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    exact absurd ((Submodule.eq_bot_iff N).1 h _ ⟨Φ, hΦ, rfl⟩) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Local

section Ram

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

theorem ramMaps_of (hI : IndIrredNarrow) : RamMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν H hν
  exact ⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h,
    fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h,
    fun Ψ _ h => pRam'_equiv Ψ h,
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam_add H hν h h₁ c) (fun _ h => pRam_mem H hν h)
      (fun Φ h h₁ => ⟨_, omA_mem_SB ν β 1 h₁ h, pRam_equiv Φ h₁⟩) (pRam_ne_zero H),
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam'_add H h h₁ c) (fun _ h => pRam'_mem H h)
      (fun Ψ h h₁ => ⟨_, omB_mem_SB ν α 1 h₁ h, pRam'_equiv Ψ h₁⟩) (pRam'_ne_zero H)⟩

end Ram

section Fin

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] PositivityTheory.ThK.SplitAsm.measFv PositivityTheory.ThK.SplitAsm.borelFv

theorem finRam_of (hR : RamMaps) (hRN : RamNonzero) (hI : IndIrredNarrow) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts) :
    FinRam := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hP : v ∈ B.P := hT.chars.sub hv
  obtain ⟨hα, hβ, hν, hcond, hram, -⟩ := hC F E B X a a' v (B.τ ⟨v, hP⟩) hT.chars
  have hS : HidaSetting a a' (unifAt v) (chrW X.α (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)) (chrW X.ν (B.τ ⟨v, hP⟩)) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon'⟩ := hR (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨Φ0, hΦ0, hnz⟩ := hRN (Fv F v) a a' _ _ _ _ hS (hram hv)
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, hbas, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v (B.τ ⟨v, hP⟩)
  obtain ⟨rfl, rfl, rfl⟩ := hbas hP rfl
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pRam a a' (unifAt v) (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.β (B.τ ⟨v, hP⟩)))
    (pRam' a a' (chrW X.ν (B.τ ⟨v, hP⟩)) (chrW X.α (B.τ ⟨v, hP⟩)))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨Φ0, hΦ0, hnz⟩
    (fun N hN hst => irred_of_setting hI hS N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro hv'; exact absurd hv hv'
  · intro hv' _
    refine ⟨ι, ι', hW, hB, hvac, hvac', fun φ hφ φ' hφ' => ?_⟩
    rw [oneMaps_p, oneMaps_p']
    refine ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · have := congrArg Subtype.val h
      erw [hp φ hφ, hp' φ' hφ'] at this
      exact this
    · erw [hp φ hφ, hp' φ' hφ']
      exact h

end Fin

theorem finRam_of_narrow :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
      (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
      (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinRam :=
  fun NB => finRam_of (ramMaps_of (indIrredNarrow_of NB)) ramified_map_ne_zero (indIrredNarrow_of NB) split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts

end GlobalTheory.CompanionTheory.SplitNarrow
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SocleFrob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_smul_id {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) k) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  have hs' : GroundTheory.Automorphic.IsSmooth ρ := hs
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm

theorem isIrreducible_piTensor {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    exists_eq_smul_id _ (x a).2.rep.smooth (x a).2.rep.irr φ hφ

theorem jm_ne_zero_of_isSocle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  intro k _ _ _ _ h N x hd V _ _ π _ _ hS
  obtain ⟨hi, f, hf, -⟩ := hS
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ Zc.jm x hd π :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (x a).1) hd) (isIrreducible_piTensor x) f
      ⟨v, fun h0 => hv (hf (h0.trans (map_zero f).symm))⟩
  exact ENat.one_le_iff_ne_zero.1 h1

end GlobalTheory.CompanionTheory.SocleFrob

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.product_transpose_inverse_dual_reverse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x (Fin.rev a))).1 = N, Nonempty (Representation.Equiv ((prodIrr x hd).comp (thetaW k N)) (prodIrr (fun a => dualCl (x (Fin.rev a))) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | exact GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.TwSide

section Generic

variable {G : Type} [Group G]

end Generic

section Diag

variable {L : Type} [Field L]

theorem thetaGL_diagT (c : L →+* L) {n : ℕ} (u : Fin n → Lˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT L (Fin n) u) =
      GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.map (c : L →* L) (u i.rev)⁻¹ := by
  apply Units.ext
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero,
      mul_zero]

theorem exists_diagT {n : ℕ} (g : GL (Fin n) L) (h : ∀ i j : Fin n, i ≠ j → g.val i j = 0) :
    ∃ s : Fin n → Lˣ, g = GlobalTheory.SmGL.diagT L (Fin n) s := by
  have hne : ∀ i, g.val i i ≠ 0 := by
    intro i h0
    have h1 : (g.val * (g⁻¹).val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [h i k hk, zero_mul]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

end Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_diagT_of_mem_TO {n : ℕ} {w : Pl E} {τ : GLw n w} (hτ : τ ∈ TO n w) :
    ∃ v : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (v i : w.adicCompletion E) = 1) ∧
      τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
  obtain ⟨v, hv⟩ := exists_diagT τ hτ.1
  refine ⟨v, fun i => ?_, hv⟩
  have h := hτ.2 i
  rw [hv, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at h
  exact h

theorem nrmL_diagT {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (u : Fin n → (w.adicCompletion E)ˣ) :
    nrmL n w (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n)
        fun i => u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ := by
  rw [nrmL, if_neg hw, thetaGL_diagT, ← map_mul]
  rfl

theorem ordL_norm_entry (hU : Unr E) {n : ℕ} {w : Pl E} (u : Fin n → (w.adicCompletion E)ˣ) (y : Fin n → ℤ)
    (hu : ∀ i, ordL (u i : w.adicCompletion E) = y i) (i : Fin n) :
    ordL ((u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = nv y i := by
  obtain ⟨-, -, hcv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hinv : ordL (((u i.rev)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    have h1 := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i.rev).ne_zero ((u i.rev)⁻¹).ne_zero
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one, hu] at h1
    omega
  have hmap : ordL ((Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    rw [← hinv]
    exact GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (hcv _)
  rw [Units.val_mul, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i).ne_zero (Units.ne_zero _), hu, hmap]
  simp only [nv]
  omega

end GlobalTheory.CompanionTheory.TwSide
end
end

section

open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT

theorem _root_.GlobalTheory.T.constant_term_multiplicative : CtMul := by
  first | exact @GlobalTheory.CompanionTheory.CtMulSplit.ctMul | exact GlobalTheory.CompanionTheory.CtMulSplit.ctMul | (intros; apply GlobalTheory.CompanionTheory.CtMulSplit.ctMul <;> assumption)
end

section

open NumberField GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

theorem _root_.GlobalTheory.T.mu_character_exists : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e) → MuEx := by
  first | exact @GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | exact GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists | (intros; apply GlobalTheory.CompanionTheory.MuOpen.muEx_of_exists <;> assumption)
end
