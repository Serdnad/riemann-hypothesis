module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle599
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle513
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerConjTransport
theorem kernel_conjugate_transport_top_degree : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u) := by
  intro hP hI hDict hDepth
  obtain ⟨CF0, hb0⟩ := BigC.and hDict hDepth
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, hb1⟩ := hb0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, hb2⟩ := hb1 ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨hD, -⟩ := hb2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  clear hb0 hb1 hb2 hDict hDepth
  intro Φ β d hocc c j f hf σ ρ hρ
  obtain ⟨-, τe, ⟨hk, ⟨e, -, hτ1, -⟩, hτ3⟩, hdτ⟩ := hocc
  have hdp : DefPair D.R.m (Pair.top A.μ0 (j : ℕ) : Pair T) := by
    show (j : ℕ) + 1 ≤ D.R.m
    omega
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, hr, -, hjet⟩ :=
    hD A.μ0 (.top A.μ0 j) hdp _ (d.1 j) hk ((hτ3 d hdτ).1 j) ((hτ1 d hdτ).1 j).2.2 ((hτ1 d hdτ).1 j).1
      (ch.S.ptTop c j) (ch.S.ptTop c (j + 1))
  have hJ := (wtOK_of_defPair ch.G (.top A.μ0 j) hdp).2
  have he0 := ch.S.Z.e0_is _ hdp
  have hev := even_rank_mul ch.G _ hdp
  have hper : ∀ τ : D.what₂.Tau, period ch.S.Z.δ τ ≠ 0 := fun τ => period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) τ
  have hkk := kkMap_top_eq ch.S.Z A.μ0 j (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) _ hJ hper hjet
  obtain ⟨ρ', hρσ, hlam⟩ := GlobalTheory.T.exists_algebraicNumbers_extension_curveField_conjLattice D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 σ ρ hρ
  obtain ⟨t', ht'⟩ := ((hI D).t0Ex D.host.ccK ch.S.Z.δ ch.S.Z.crv).2 (GlobalTheory.KerConjMean.fld D ch.S.Z.δ ch.S.Z.t0) ρ
    (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))) (IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp)))
  have hDj := GlobalTheory.T.thetaCombinationJets_algebraic_conj_eq_conjSeries D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ _ hev _ he0 Ls Lt hLs hLt κ hκ _ n hk r s hs ρ'
  refine ⟨ρ', ch.S.Z.e0 (.top A.μ0 j), Ls, Lt, κ, _, n, r, s, hev, he0, hLs, hLt, hκ, hk, hs, hr, hlam, ⟨t', ht'⟩, hJ,
    fun u => ?_⟩
  rw [GlobalTheory.T.jetOperator_rationalForm_conj_eq_conjTable _ _ _ _ σ ρ' f hJ (fun m => (hDj m).1) hρσ (fun u => by rw [← hkk]; exact hf u) u]
  congr 1
  congr 1
  funext m
  exact (hDj m).2
end GlobalTheory.KerConjTransport
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.kernel_conjugate_transport : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u) := by
  first | exact @_root_.GlobalTheory.KerConjTransport.kernel_conjugate_transport_top_degree | exact _root_.GlobalTheory.KerConjTransport.kernel_conjugate_transport_top_degree | (intros; apply _root_.GlobalTheory.KerConjTransport.kernel_conjugate_transport_top_degree <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.RealMapsChars
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealMapsChars in
theorem GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  intro hP F E _ _ _ _ _ σ B a a' Γ Xa Xb oa oa' ob ob' R hA hB hR
  obtain ⟨hV, hV'⟩ := GlobalTheory.T.weilOperators_eq_at_realPlaces_same_exponents F E σ B a a' Γ Xa Xb oa oa' ob ob' hA hB
  have lV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, 1) Φ = ob (g, 1) Φ :=
    fun g hg Φ hΦ => hV g 1 hg one_mem_uAt Φ hΦ
  have lV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, 1) Φ = ob' (g, 1) Φ :=
    fun g hg Φ hΦ => hV' g 1 hg one_mem_uAt Φ hΦ
  have lW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (1, h) Φ = ob (1, h) Φ :=
    fun h hh Φ hΦ => hV 1 h one_mem_uAt hh Φ hΦ
  have lW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (1, h) Φ = ob' (1, h) Φ :=
    fun h hh Φ hΦ => hV' 1 h one_mem_uAt hh Φ hΦ
  have bV : ∀ g ∈ UAt σ Γ.V (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (g, 1) Φ = oa (g, 1) Φ :=
    fun g hg Φ hΦ => (lV g hg Φ hΦ).symm
  have bV' : ∀ g ∈ UAt σ Γ.V' (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (g, 1) Φ = oa' (g, 1) Φ :=
    fun g hg Φ hΦ => (lV' g hg Φ hΦ).symm
  have bW : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), ob (1, h) Φ = oa (1, h) Φ :=
    fun h hh Φ hΦ => (lW h hh Φ hΦ).symm
  have bW' : ∀ h ∈ UAt σ Γ.W (evI F), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), ob' (1, h) Φ = oa' (1, h) Φ :=
    fun h hh Φ hΦ => (lW' h hh Φ hΦ).symm
  refine ⟨⟨hR.quot.onto, ?_, ?_⟩, ⟨hR.quot'.onto, ?_, ?_⟩, ?_, ?_, hR.nontriv, ?_⟩
  · intro γ hγ f hf f₁ h
    exact hR.quot.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot.cpt k hk f hf f₁ (acts_of_eqOn (bV k hk.1) h)
  · intro γ hγ f hf f₁ h
    exact hR.quot'.lie γ hγ f hf f₁ (actsD_of_eqOn (fun t => bV' _ (hγ.2 _)) h)
  · intro k hk f hf f₁ h
    exact hR.quot'.cpt k hk f hf f₁ (acts_of_eqOn (bV' k hk.1) h)
  · intro γ hγ f hf f' hf' f₁ f₁' h h'
    exact hR.lie γ hγ f hf f' hf' f₁ f₁' (actsD_of_eqOn (fun t => bW _ (hγ.2 _)) h)
      (actsD_of_eqOn (fun t => bW' _ (hγ.2 _)) h')
  · intro k hk f hf f' hf' f₁ f₁' h h'
    exact hR.cpt k hk f hf f' hf' f₁ f₁' (acts_of_eqOn (bW k hk.1) h) (acts_of_eqOn (bW' k hk.1) h')
  · intro N h1 h2
    refine hR.irred N (fun γ hγ f hf f₁ h => h1 γ hγ f hf f₁ (actsD_of_eqOn (fun t => lW _ (hγ.2 _)) h))
      (fun k hk f hf f₁ h => h2 k hk f hf f₁ (acts_of_eqOn (lW k hk.1) h))
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @_root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | exact _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent | (intros; apply _root_.GlobalTheory.RealMapsChars.real_embeddings_of_characters_of_same_exponent <;> assumption)
end
end

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
open scoped TensorProduct

theorem GlobalTheory.RealQuotBot.real_quotient_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  intro hH hP hK hLM D ψ θ hψ hθ A A' WW FA FA' FW a b had hsA hsA' hsW hex Pr q q' hq hq' hfac
  obtain ⟨α, β, hT, hE⟩ := hex
  obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, hfac2⟩ := hfac α β hT hE
  obtain ⟨Pf, r, r', e, hr, hr', hpA, hpB⟩ := hfac2 _ _ _ _ _ _ _ hm
  have hPi : Nontrivial Pi := hm.irred.1
  have hall : ¬ ∀ z : Pr ⊗[ℂ] Pf, z = 0 := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
    exact hz (by rw [← e.apply_symm_apply z, h (e.symm z), map_zero])
  have hPr : Nontrivial Pr := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add u v hu hv => rw [hu, hv, add_zero]
  have hPf : Nontrivial Pf := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add u v hu hv => rw [hu, hv, add_zero]
  obtain ⟨y, hy⟩ := exists_ne (0 : Pf)
  obtain ⟨f, hf, hfy⟩ := hr y
  obtain ⟨f', hf', hfy'⟩ := hr' y
  have hf0 : f ≠ 0 := by rintro rfl; exact hy (by rw [← hfy, map_zero])
  have canc : ∀ x x' : Pr, e (x ⊗ₜ y) = e (x' ⊗ₜ y) → x = x' := by
    intro x x' h
    by_contra hne
    have h2 : (x - x') ⊗ₜ[ℂ] y = 0 := by
      rw [TensorProduct.sub_tmul]; exact sub_eq_zero.2 (e.injective h)
    exact GlobalTheory.RealQuotBot.tmul_ne_zero (sub_ne_zero.2 hne) hy h2
  have sA := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A FA τ (hsA τ)
  have sA' := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A' FA' τ (hsA' τ)
  have sW := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D WW FW τ (hsW τ)
  obtain ⟨hTA, hcoA, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ true A WW FA FW β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA
    (fun τ => ⟨(hE τ).2, GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hE τ).1 (hE τ).2⟩) Pi rf rl p hm.mapA
  obtain ⟨hTB, hcoB, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false A' WW FA' FW α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB
    (fun τ => ⟨(hE τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ (b τ) (a τ) (hE τ).2 (hE τ).1⟩) Pi rf rl p' hm.mapB
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.definiteBottomTriple_weight_natural D ψ θ A A' WW FA FW a b α β ωA hθ hsA hsW hT hE hm.weilA ⟨f, hf, hf0⟩
  have kA : GlobalTheory.RealQuot.coinv true FA FW (fun τ => b τ - a τ) ≤ LinearMap.ker q := by
    intro P hP
    have h := hcoA f hf P hP
    rw [hpA f hf P, hfy] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have kB : GlobalTheory.RealQuot.coinv false FA' FW (fun τ => a τ - b τ) ≤ LinearMap.ker q' := by
    intro P hP
    have h := hcoB f' hf' P hP
    rw [hpB f' hf' P, hfy'] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have hrel : ∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt WW τ,
      q (GlobalTheory.RealQuot.actT true FA FW b τ Y P) = q' (GlobalTheory.RealQuot.actT false FA' FW a τ Y P') := by
    intro P P' hPP τ Y hY
    have h1 := hTA f hf τ Y hY P
    have h2 := hTB f' hf' τ Y hY P'
    rw [hpA f hf, hpA f hf, hfy] at h1
    rw [hpB f' hf', hpB f' hf', hfy'] at h2
    refine canc _ _ ?_
    rw [h1, h2, hPP]
  have hrow := GlobalTheory.T.definite_bottom_row_transport_contragredient D A A' WW FA FA' FW b a n₀ Pr q q' sA sA' sW
    (fun τ => by
      have hc : ((A.rank : ℚ) + (A'.rank : ℚ)) = (WW.rank : ℚ) := by exact_mod_cast had
      rw [hn₀ τ, hc]) hrel
  have hdet : ∀ κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ,
      GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) ≠ 0 := by
    intro κ
    unfold GlobalTheory.MinorFrame.detChar
    exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (GlobalTheory.RealQuotBot.det_unitary_ne_zero (κ τ))
  let σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr := fun κ =>
    if h : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ).map (starRingEnd ℂ))).toLinearMap) then
      (LinearMap.ker q).liftQ _ h ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap else 0
  have hσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ) P,
      σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P) =
        q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) := by
    intro κ P
    have hk : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ))).toLinearMap) := by
      intro P₀ hP₀
      rw [LinearMap.mem_ker] at hP₀ ⊢
      have h := hrow κ P₀ 0 (by rw [hP₀, map_zero])
      rw [map_zero, map_zero] at h
      exact (smul_eq_zero.1 h.symm).resolve_left (hdet κ)
    have e1 : (q.quotKerEquivOfSurjective hq).symm (q P) = Submodule.Quotient.mk P := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [σ, dif_pos hk, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, Submodule.liftQ_apply, AlgHom.toLinearMap_apply]
  refine ⟨hPr, n₀, σ, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D true A WW FA FW (fun τ => b τ - a τ) n₀ Pr q sA sW (fun τ => by simp only [if_true]; exact hn₀ τ) kA
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D false A' WW FA' FW (fun τ => a τ - b τ) n₀ Pr q' sA' sW
      (fun τ => by simp only [Bool.false_eq_true, if_false]; rw [hn₀ τ]; ring) kB
  · intro κ P _
    rw [hσ]
  · intro κ P' _
    obtain ⟨P, hP⟩ := hq (q' P')
    rw [hrow κ P P' hP, ← hP, hσ]
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
open scoped TensorProduct

theorem _root_.GlobalTheory.T.real_quotient_bottom_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  first | exact @_root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | exact _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | (intros; apply _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
namespace GlobalTheory.AvgTypeOther
section SeriesClosure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open GlobalTheory.SeriesToClosure
open scoped TensorProduct InnerProductSpace
end SeriesClosure
section ClosureSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
open GlobalTheory.ClosureSeries
end ClosureSeries
open Formalism.MainNotions.S Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum in
theorem isTypeAt_average_other_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ τ' hne ψ hψ hty e he
  have hec : Continuous e := by
    obtain ⟨F, -, h1, h2, -⟩ := he
    exact h2 _ h1
  have hHC := hPr.harishChandraModules
  have hCW := hPr.casselmanWallach
  have hUn := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have hT := hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') ψ hHC hθ hψ hty
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * Formalism.REAL.toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.LowTypeDetermined.conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA := GlobalTheory.AvgOtherPlace.hasTypeAt_avgF (Formalism.REAL.muK (N.M.ε τ)) hθ hne hκ hU hec hψ.cont hT
  have hAs := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (Formalism.REAL.KG (N.M.ε τ)) (Formalism.REAL.muK (N.M.ε τ)) _
    hκ hU e hec ψ hψ
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP', hJ', -⟩ := hty
  exact isTypeAt_of_hasTypeAt_model θ N.V τ' (N.S τ') _ hUn hHC hCW hθ H σ lam ε P hE
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD) hD hP' hJ' hAs hA
end GlobalTheory.AvgTypeOther
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

theorem _root_.GlobalTheory.T.average_isTypeAt_other_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | exact _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place | (intros; apply _root_.GlobalTheory.AvgTypeOther.isTypeAt_average_other_place <;> assumption)
end
end
