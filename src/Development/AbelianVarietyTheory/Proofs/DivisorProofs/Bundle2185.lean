module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModulusStandardThetaPresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
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
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  first | exact @GlobalTheory.BrPairBound.inf_bound | exact GlobalTheory.BrPairBound.inf_bound | (intros; apply GlobalTheory.BrPairBound.inf_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.OffVLocalWeights.exists_localizing_weight | exact GlobalTheory.OffVLocalWeights.exists_localizing_weight | (intros; apply GlobalTheory.OffVLocalWeights.exists_localizing_weight <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.cosetVector_blockLevel_unimodular_eigen : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  first | exact @GlobalTheory.BotPairSmall.cvec_eig | exact GlobalTheory.BotPairSmall.cvec_eig | (intros; apply GlobalTheory.BotPairSmall.cvec_eig <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.weilAction_cosetVector_fixed_principalCongruence : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ k ∈ intG D a, CongOne D (D.host.conj • 𝔪) k → W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
  first | exact @GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne | exact GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne | (intros; apply GlobalTheory.BotPairSmall.CvFix.om_cvec_of_congOne <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.conjugateModulus_standardTheta_presentation : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hb : IsCoprime (D.host.conj • 𝔪) D.host.𝔟) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ Q : ℕ, Ideal.absNorm 𝔪 = Q → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D (D.host.conj • 𝔪) (r⁻¹ * k)) → Pres D ⊤ δ Q e0 (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0)) := by
  first | exact @GlobalTheory.BotPairSmall.pres_conj_std | exact GlobalTheory.BotPairSmall.pres_conj_std | (intros; apply GlobalTheory.BotPairSmall.pres_conj_std <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetMove

theorem wd_wd_norm (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  have hn : ∀ x : VC D N N', ‖wdPh D T x‖ = 1 := fun x => by
    simp [wdPh, ee, Complex.norm_exp]
  have hc : Hf D T b a = (starRingEnd ℂ) (Hf D T a b) := by

    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · rw [norm_mul, norm_div, norm_mul, hn, hn, hn, Complex.norm_exp, hc]
    have : (((Real.pi : ℂ) * ((starRingEnd ℂ) (Hf D T a b) - Hf D T a b) / 2)).re = 0 := by
      simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.div_re]
    rw [this]; simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this



theorem om_cosetV_block : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hcop _ h hh hblk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨G, hGdef⟩ : ∃ G, G = Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := ⟨_, rfl⟩

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd, hcen⟩ := GlobalTheory.T.exists_skew_lattice_mover_with_determinant D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hJ : W.Om 1 g' e0 = χ • G := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (FixKey.suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using FixKey.zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm, hχ, hGdef]
    rfl
  have hc0 : χ ≠ 0 := by rw [hχ]; exact Units.ne_zero _
  have hJe : G = χ⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hgT : W.Om 1 g' e0 ∈ TT D (tor0 D ⊤ δ) a d := W.maps 1 g' e0 hT
  have hJT : G ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact FixKey.TT_smul _ hgT

  obtain ⟨xh, -, hxh⟩ := VacInt.om_vac_right he hT W ((mem_intG h).1 hh)
  obtain ⟨uh, huh⟩ : ∃ u : ℂ, u = ((W.chV.f xh ^ W.ep : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huh] at hxh
  have hhG : W.Om 1 h G = uh • G := by
    have e1 := W.mul 1 1 h g' e0 hT
    have e2 := W.mul 1 1 g' h e0 hT
    rw [mul_one] at e1 e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, hcen, e2, hxh, W.smul _ _ _ _ hT, smul_comm]
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock D 𝔪 h𝔪 hcop had h hh hblk
  obtain ⟨xk, -, hxk⟩ := VacInt.om_vac_left he hT W ((mem_intG k).1 hk)
  obtain ⟨uk, huk⟩ : ∃ u : ℂ, u = ((W.chV'.f xk ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huk] at hxk
  have hkG : W.Om k 1 G = uk • G := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one] at e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, e2, hxk, W.smul _ _ _ _ hT, smul_comm]
  have nuh : ‖uh‖ = 1 := by
    rw [huh, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV.unitary, one_zpow]
  have nuk : ‖uk‖ = 1 := by
    rw [huk, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV'.unitary, one_zpow]

  obtain ⟨x₀, hx₀⟩ : ∃ x, x = unitBlock D 0 a d := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁, hl₁⟩ := W.lift 1 h x₀ G hJT
  obtain ⟨m₂, hm₂, hl₂⟩ := W.lift k 1 x₀ G hJT
  obtain ⟨Y₁, hY₁⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y = ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * x₀.map (inc D) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y =
    x₀.map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  have hkx' : ∀ i j, (Y₁ - Y₂) i j ∈ hatId D 𝔪 := by rw [hY₁, hY₂, hx₀]; exact hkx
  obtain ⟨z, hz⟩ := VacMove.MI_approx (cc := ⊤) top_ne_bot Y₂ (m₁ * m₂) (Nat.mul_pos hm₁ hm₂)
  obtain ⟨w, hw𝔪, hw⟩ := GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat D 𝔪 (Y₁ - Y₂) hkx' m₁ hm₁
  have hc2 : CloseTo D ⊤ m₂ (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ z := by
    have := hz.of_dvd (m := m₂) (dvd_mul_left _ _)
    intro i j
    obtain ⟨y, hy, e⟩ := this i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₂]; simp
  have hc1 : CloseTo D ⊤ m₁ ((1 : GA D a) : GL (Fin a) (AE D)) (h : GL (Fin d) (AE D)) x₀ (z + w) := by
    have h3 := (hz.of_dvd (m := m₁) (dvd_mul_right _ _)).add hw
    have key : z.map (inc D) - Y₂ + (w.map (inc D) - (Y₁ - Y₂)) = (z + w).map (inc D) - Y₁ := by
      ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add (f := _)]; abel
    rw [key] at h3
    intro i j
    obtain ⟨y, hy, e⟩ := h3 i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₁]; simp
  have hWh := hl₁ (z + w) hc1
  have hWk := hl₂ z hc2
  rw [hhG, FixKey.wd_smul, VacMove.pt_add] at hWh
  rw [hkG, FixKey.wd_smul] at hWk

  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_norm D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  rw [← hGdef] at hJB
  have hwB := (GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪).2
  have hfix : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ w) G = G := VacMove.wd_fix h1 hc hBk hJB hwB
  have hφ0 : φ ≠ 0 := by intro h0; rw [h0, norm_zero] at hφ1; exact zero_ne_one hφ1
  have hsum := hφ G
  rw [hfix] at hsum
  have hzw : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z + pt D (tor0 D ⊤ δ) δ w) G =
      φ⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
  have huk0 : uk ≠ 0 := by rw [huk]; exact Units.ne_zero _
  refine ⟨uh * φ⁻¹ * uk⁻¹, by rw [norm_mul, norm_mul, norm_inv, norm_inv, nuh, hφ1, nuk]; simp, k, hk, ?_⟩
  have hWT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G ∈ TT D (tor0 D ⊤ δ) a d :=
    GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT
  unfold cosetV
  rw [← hx₀, ← hGdef]
  rw [W.smul _ _ _ _ hWT, W.smul _ _ _ _ hWT]
  change _ • W.Om 1 h (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G) = _ • _ • W.Om k 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G)
  rw [hWh, hWk, hzw, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FunObj.CosetMove
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.standardTheta_datum_presentation_level_norm : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → IsCoprime 𝔪 D.host.𝔟 → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 0 R) := by
  first | exact @GlobalTheory.FunObj.StdDatum.pres_stdSum | exact GlobalTheory.FunObj.StdDatum.pres_stdSum | (intros; apply GlobalTheory.FunObj.StdDatum.pres_stdSum <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.weil_operator_for_weyl_element : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  first | exact @GlobalTheory.WeylFour.weyl_hasOp | exact GlobalTheory.WeylFour.weyl_hasOp | (intros; apply GlobalTheory.WeylFour.weyl_hasOp <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.weyl_element_operator_bijective : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChangeBij.HasOpB ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  first | exact @GlobalTheory.WeylBij.weyl_hasOpB | exact GlobalTheory.WeylBij.weyl_hasOpB | (intros; apply GlobalTheory.WeylBij.weyl_hasOpB <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedTr
variable {D : D7}

theorem heisO_add_eq (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ u : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T (w₀ + u) F = ψ (-symplOH S T w₀ u) • heisO ψ S T w₀ (heisO ψ S T u F) := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc]
  have h1 : ψ (-symplOH S T w₀ u) * ψ (symplOH S T w₀ u) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (-(ψ (symplOH S T w w₀) * ψ (symplOH S T w u) * F (w + (w₀ + u)))) * h1

theorem closeTo_of_mul {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {k m : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (k * m) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨t, ht, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t, ?_, ?_⟩
  · have : (k : Formalism.MainNotions.StandardLatticesGL3.AE D) * t = k • t := by rw [nsmul_eq_mul]
    rw [this]; exact AddSubgroup.nsmul_mem _ ht k
  · rw [e]; push_cast; ring

theorem moved_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • om (g, h) (heisO ψ S T (finPt hS hT r z) f₀) =
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset χS χT om hom x y g h hg hh f₀ hf₀ z
  have hF := hom.om_pres (g, h) f₀ hf₀
  obtain ⟨n₁, hn₁, H₁⟩ := GlobalTheory.T.heisenbergTranslate_fixes_theta_deepLevel ψ θ S T hS hT cc δ r hset x y g h hg hh _ hF z
  obtain ⟨n₂, hn₂, H₂⟩ := GlobalTheory.T.standardChar_halfSymplectic_movedFinitePoint_trivial ψ θ S T hS hT cc δ r hset x y g h hg hh z
  obtain ⟨n₃, hn₃, H₃⟩ := GlobalTheory.T.exists_level_curvePhase_eq_of_close cc δ hset.crv x y z
  refine ⟨n₁ * n₂ * n₃, by positivity, fun z' hz' => ?_⟩
  have c1 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₁ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₂ * n₃) (by rwa [show n₂ * n₃ * n₁ = n₁ * n₂ * n₃ by ring])
  have c2 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₂ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₃) (by rwa [show n₁ * n₃ * n₂ = n₁ * n₂ * n₃ by ring])
  have c3 : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n₃ (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' :=
    closeTo_of_mul (k := n₁ * n₂) (by rwa [show n₁ * n₂ * n₃ = n₁ * n₂ * n₃ by ring])
  rw [hom.om_heis g h _ f₀ hf₀, H₃ z' c3]
  have e : actO S T g h (finPt hS hT r z) =
      finPt hS hT r z' + (actO S T g h (finPt hS hT r z) - finPt hS hT r z') := by abel
  have hψ : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
    have h2 := H₂ z' c2
    have h0 : ψ (-symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) *
        ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h2, mul_one] at h0
  rw [e, heisO_add_eq, H₁ z' c1, hψ, one_smul]

end GlobalTheory.MovedTr
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.readsGaussian_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  first | exact @GlobalTheory.NormExact.reads_smul_const_unique | exact GlobalTheory.NormExact.reads_smul_const_unique | (intros; apply GlobalTheory.NormExact.reads_smul_const_unique <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_heckeCharacter_of_thetaModelCharacter : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ), (e = 1 ∨ e = -1) →
  ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ N ∧ HasFinPart χ c e := by
  first | exact @GlobalTheory.HeckeUChar.exists_hecke_of_heckeU | exact GlobalTheory.HeckeUChar.exists_hecke_of_heckeU | (intros; apply GlobalTheory.HeckeUChar.exists_hecke_of_heckeU <;> assumption)
end
