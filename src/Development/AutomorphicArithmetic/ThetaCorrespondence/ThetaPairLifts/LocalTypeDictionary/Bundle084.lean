module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoConst
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumSmallStageEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsSeesawIntertwinersOfTriple
public import Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftPureTensorOfIsFinF
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle080
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle930
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle820
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle781
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle956
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle192
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle082
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.rallis_bottom_formula_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω' : ℂ, Ω' ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T', X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g = Ω' * u * P'.coord h T' := by
  intro hPr hK hM hI hB
  have hA := _root_.GlobalTheory.T.bottom_classSum_smallStage_eq hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := hA
  have hB' := _root_.GlobalTheory.T.smallStage_bottomKernel_eq_term hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := hB'
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₁, h1, HA⟩ := hA W hψ i j A A' WW X δ t0 hX
  obtain ⟨Ω₂, h2, HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  refine ⟨Ω₁ * Ω₂, mul_ne_zero h1 h2, fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HB⟩ := HB s Q P P' hP
  refine ⟨u, hu, huQ, huU, fun ea ed h g hg T' => ?_⟩
  have hgx : ∀ x : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a), ∃ g', GlobalTheory.BotFormula.IsFinPt A' g' x.out :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one A' hX.std'.1 x.out ea.symm
  choose gx hgx using hgx
  rw [HA s Q P P' hP ea ed h g hg gx hgx T', Pair.coord]
  have e : ∀ x : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ * X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) =
        (Ω₂ * u) * (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ * P'.term x.out h T') := by
    intro x; rw [HB ea ed h g hg x.out (gx x) (hgx x) T']; ring
  simp_rw [e]
  rw [← mul_finsum]
  ring
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_bottom_formula_small : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω' : ℂ, Ω' ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T', X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g = Ω' * u * P'.coord h T' := by
  first | exact @_root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank | exact _root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank | (intros; apply _root_.GlobalTheory.BotFormula.rallis_bottom_formula_small_rank <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.StageGeo
variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}
theorem geometric_stage_constant_ratio (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {a b : D.what₂.Tau → ℚ}
    (hd : ∀ t : T, IsTriple A A' WW (α t) (β t) ∧ (∀ τ, HasInfExp D (α t) τ (a τ) ∧ HasInfExp D (β t) τ (b τ)) ∧
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) P) = X.ker ψ θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) P) = X.ker' ψ θ t P h g)
    {lam : T → ℂ} (hF : GlobalTheory.ConstRatio.Factor X ψ θ lam) {t₁ t₂ : T} {X₁ X₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E}
    (r₁ : Reads α β S Bs t₁ X₁) (r₂ : Reads α β S Bs t₂ X₂) {R om₁ om₁' Rf₁ om₂ om₂' Rf₂} {c₁ c₂ : ℂ}
    (m₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₁ om₁ om₁' R Rf₁) (m₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₂ om₂ om₂' R Rf₂)
    (k₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₁ om₁ om₁' R Rf₁ c₁) (k₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₂ om₂ om₂' R Rf₂ c₂) :
    c₁ * lam t₂ = c₂ * lam t₁ := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  obtain ⟨g, g0, hg⟩ := exists_vac (ε := true) hG.pairA hG.latA hX.isVac
  obtain ⟨g', g0', hg'⟩ := exists_vac (ε := false) hG.pairB hG.latB hX.isVac'
  have hco : ∀ {κ : Type} (T₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
      {φ vac : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (κ → Fv D.host.F v) → ℂ}, (∀ v ∉ T₀, φ v = vac v) →
      ∀ᶠ v in Filter.cofinite, φ v = vac v := fun T₀ _ _ h =>
    Filter.Eventually.mono T₀.finite_toSet.compl_mem_cofinite fun v hv => h v hv
  obtain ⟨Φ, Φ', hΦ, hΦ', eΦ, eΦ'⟩ : ∃ (Φ : PolF D WW.rank A.rank →ₗ[ℂ] SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)))
      (Φ' : PolF D WW.rank A'.rank →ₗ[ℂ] SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank))),
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧ LinearMap.range Φ' = Γ.M'.Pol Bs.ψ Bs.emb ∧
      (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) → ∀ P,
        thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
          fockF ψ θ true FA FW (thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P) ∧
      ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) → ∀ P,
        thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ' P) φ) =
          fockF ψ θ false FA' FW (thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ)) P := by
    obtain ⟨φ, φ', s, s', v, v', n, n', -, e, e'⟩ := exists_fin hX hG r₁ m₁ hg hg'
    obtain ⟨Φ, h1, h2⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ true A WW _ hX.rank Bs Γ.V Γ.W Γ.M hG.pairA θ hθ FA FW hG.cartA g g0 φ s (hco _ v) n
      (e ▸ (hd t₁).2.2.1)
    obtain ⟨Φ', h1', h2'⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ false A' WW _ hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB θ hθ FA' FW hG.cartB g' g0' φ' s'
      (hco _ v') n' (e' ▸ (hd t₁).2.2.2.1)
    exact ⟨Φ, Φ', h1, h1', h2, h2'⟩
  obtain ⟨-, Pi, p, p', J, -, hJ, -, hI, hI', P', hP', hint⟩ := hF
  have mP' : Φ' P' ∈ Γ.M'.Pol Bs.ψ Bs.emb := hΦ' ▸ LinearMap.mem_range_self _ _
  obtain ⟨f, mf, ef⟩ : R.p' (Φ' P') ∈ (Γ.M.Pol Bs.ψ Bs.emb).map R.p := by rw [m₁.real.quot.onto]; trivial
  obtain ⟨P, rfl⟩ : f ∈ LinearMap.range Φ := hΦ ▸ mf
  obtain ⟨Pr, qm, qm', -, -, hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW a b
  have key : ∀ t Xc om om' Rf c, Reads α β S Bs t Xc → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c → lam t • p P = c • p' P' := by
    intro t Xc om om' Rf c r m k
    obtain ⟨hT, hE, -, -, hk, hk'⟩ := hd t
    obtain ⟨Pim, rf, rl, pm, pm', hmm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT
      (hLM _ _ hT hE).1 (X.ω t) (X.ω' t) (hX.weil t) (hX.weil' t)
    obtain ⟨φ, φ', s, s', v, v', -, -, l, e, e'⟩ := exists_fin hX hG r m hg hg'
    obtain ⟨cA, cB, hO, dA, dB⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D ψ θ hθ T A A' WW X FA FA' FW hX.rank Bs Γ hG Xc om om' m.triple (X.ω t) (X.ω' t)
      (by rw [r.eα, r.eβ]; exact hX.weil t) (by rw [r.eα, r.eβ]; exact hX.weil' t)
    rw [r.eα, r.eβ] at hO
    have d1 := dA _ (GlobalTheory.TensUniq.pure_mem_schA (Φ P) φ s (((hco _ v).and m.triple.geo.hM.std).mono fun v h => h.1.trans h.2))
    have d2 := dB _ (GlobalTheory.TensUniq.pure_mem_schA (Φ' P') φ' s'
      (((hco _ v').and m.triple.geo.hM'.std).mono fun v h => h.1.trans h.2))
    rw [eΦ φ s (hco _ v), ← e] at d1
    rw [eΦ' φ' s' (hco _ v'), ← e'] at d2
    have h1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors hP hK D ψ θ A A' WW FA FA' FW _ _ _ _ _ _ _ _ _ Bs Γ Xc om om' cA cB hθ hT hO hX.meas' (hX.weil' t)
      hmm.mapB.stabM.1 R Rf c m k _ mf _ mP' φ φ' s s' v v' ef l _ _ d1 d2 (fun h => by
        simp only [hk']
        exact hint t h)
    have h2 : X.I ψ θ t P = c • X.I' ψ θ t P' := by
      funext h
      have h3 := congrFun h1 h
      simp only [thetaInt, _root_.Pi.smul_apply, hk, hk'] at h3
      exact h3
    refine hJ t ?_
    rw [map_smul, map_smul, ← hI, ← hI' t P' (hint t), h2]
  have q₁ := key _ _ _ _ _ _ r₁ m₁ k₁
  have q₂ := key _ _ _ _ _ _ r₂ m₂ k₂
  refine smul_left_injective ℂ hP' ?_
  show (c₁ * lam t₂) • p' P' = (c₂ * lam t₁) • p' P'
  rw [mul_comm c₁, mul_comm c₂, mul_smul, mul_smul, ← q₁, ← q₂, smul_comm]
end GlobalTheory.StageGeo
end
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
namespace GlobalTheory.Core.Rk.LiftOnto
theorem liftInj_nonVan_typeNZ_of_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals →
    GlobalTheory.Published.UnramifiedDoublingGL →
    GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram →
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
      [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  intro hDec hDbl hGL hHecke hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull
  have hEul : GlobalTheory.Core.Rk.IP.EulerRight D := GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified hDec hGL D
  have hPole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole := GlobalTheory.LiftPoleObj.simplePole_of_hecke hHecke
  have hNe : DownNe D := _root_.GlobalTheory.T.downNe_of_eulerRight_doubling hDbl hPole D hEul
  have hNV : ∀ i t, NonVan R i t := GlobalTheory.T.thetaLift_nonvanishing_onString_of_definiteDown D hNe G Pl0 T A Ks R F hG hFull
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.T.downwardThetaLift_eigenform_is_eigenform hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.T.thetaLift_generation_finitePlaces hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.T.thetaLift_generation_at_realPlaces D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.T.downwardThetaLift_preserves_good D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.T.goodTypes_exclude_levelCharacter D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes hDec hHowe D G Pl0 T A Ks R F hG hFull
  have hOk : ∀ i t (ok : Pl D.host.E → Prop), UnrCorr R i t ok := by
    intro i t ok h hh s c y hy h1 h2 B B' hB hB' w hw _
    exact hU i t h hh s c y hy h1 h2 B B' hB hB' w hw trivial
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  exact ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hOk i A.μ0 _, hOk i A.μ0 _, hPar i A.μ0⟩),
    fun i t => ⟨hNV i t, hTNZ i t⟩⟩
end GlobalTheory.Core.Rk.LiftOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.liftInj_and_nonVan_typeNZ_of_given : GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.HeckeLPartialContinuation → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, NonVan R i t ∧ TypeNZ R i t := by
  first | exact @_root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | exact _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.Core.Rk.LiftOnto.liftInj_nonVan_typeNZ_of_hypotheses_alt <;> assumption)
end
end
