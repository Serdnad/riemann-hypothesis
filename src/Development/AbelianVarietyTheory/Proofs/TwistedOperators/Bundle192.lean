module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import GroundTheory.GlobalFields.Adele.Bundle002
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle180
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b : GL (Fin d) (Fv F v))
  (g h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), h * g = 1 →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((g).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₁₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₁).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * ((h).toBlocks₂₂).map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  ∃ G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (v.adicCompletionIntegers F), G.map (fun x => (x : Fv F v)) = Matrix.fromBlocks (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₁₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₁.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (g).toBlocks₂₂.map π * (b : Matrix (Fin d) (Fin d) (Fv F v))) ∧ IsUnit G.det := by
  first | exact @GlobalTheory.integralBlocks_leftInverse_isUnit_det | exact GlobalTheory.integralBlocks_leftInverse_isUnit_det | (intros; apply GlobalTheory.integralBlocks_leftInverse_isUnit_det <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_lieAlgebra_exp_eq_of_commute_cartanInvolution : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C → ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  first | exact @GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | exact GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan | (intros; apply GlobalTheory.ExpCartan.exists_exp_eq_of_commute_cartan <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchUniq

variable {F : Type} [Field F] [NumberField F]

def intFinInd (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator (Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) 1

theorem intFinInd_mem_SB (κ : Type) [Fintype κ] : intFinInd F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles
  have hcI := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have ho : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => hoI
  have hc : IsClosed C :=
    isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI
  have hk : IsCompact C := isCompact_univ_pi fun _ => hcI
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 := congrArg Prod.snd h
  change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2
  rwa [one_mul] at h2

theorem exists_admissible_finite_factor : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  intro F _ _ κ _
  refine ⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩
  · have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩
  · ext y
    have h1 := congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))
    have hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y := by
      funext i
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
    have h0 : intFinInd F κ (fun _ => 0) = 1 := by
      simp only [intFinInd]
      rw [Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ
        fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]
      rfl
    simp only [tens, hy, h0, mul_one] at h1
    exact h1

end GlobalTheory.ArchUniq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviRes

variable {D : D7}

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat M) = GlobalTheory.MixModel.rat Mᴴ := by
  rw [← GlobalTheory.MixModel.cT_sig]
  ext i j
  simp [GlobalTheory.MixModel.adj, GlobalTheory.MixModel.rat, Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem symplOH_add_right (S T : HSp D) (x y z : WO S T) :
    symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, map_add]

theorem symplOH_mul_rat (V W : HSp D) {s t : ℕ} (X : Matrix (Fin s) (Fin V.rank) D.host.E)
    (Y : Matrix (Fin t) (Fin V.rank) D.host.E) (hXY : X * V.gram⁻¹ * Yᴴ = 0) (q : Mx D W.rank s) (a : Mx D W.rank t) :
    symplOH V W (q * GlobalTheory.MixModel.rat X) (a * GlobalTheory.MixModel.rat Y) = 0 := by
  have hz : GlobalTheory.MixModel.rat X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hXY, GlobalTheory.MixModel.rat_zero]
  have hre : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * GlobalTheory.MixModel.rat Y) * (GlobalTheory.MixModel.gA W * (q * GlobalTheory.MixModel.rat X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q)) * GlobalTheory.MixModel.rat X := by
    rw [GlobalTheory.MixModel.adj_mul, adj_rat]
    simp only [Matrix.mul_assoc]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, hre, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero, map_zero]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem iso_iso (hs : IsIsoSplit V V' C B) : (adj D C * V.gram) * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, h0]

theorem iso_mid (hs : IsIsoSplit V V' C B) :
    (adj D C * V.gram) * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * B = 0 := hs.orth
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem periodic (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ y : Mx D W.rank r,
      f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  intro γ hγ y
  obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
  have e1 : ∀ z : Mx D W.rank r, isoPart V W C z = z * GlobalTheory.MixModel.rat (adj D C * V.gram) := fun z => rfl
  have e2 : midPart V V' W B x = (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) := rfl
  have h0 : symplOH V W (GlobalTheory.MixModel.rat γ0 * GlobalTheory.MixModel.rat (adj D C * V.gram))
      (isoPart V W C y + midPart V V' W B x) = 0 := by
    rw [symplOH_add_right, e1, e2,
      symplOH_mul_rat V W (adj D C * V.gram) (adj D C * V.gram) (iso_iso hs) (GlobalTheory.MixModel.rat γ0) y,
      symplOH_mul_rat V W (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (iso_mid hs) (GlobalTheory.MixModel.rat γ0) x,
      add_zero]
  have hq : f (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram)) + (isoPart V W C y + midPart V V' W B x)) =
      ψ (-(symplOH V W (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram))) (isoPart V W C y + midPart V V' W B x))) *
        f (isoPart V W C y + midPart V V' W B x) :=
    hf.quasi (γ0 * (adj D C * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [e1 (GlobalTheory.MixModel.rat γ0 + y), Matrix.add_mul, add_assoc, ← e1 y, ← GlobalTheory.MixModel.rat_mul, hq,
    GlobalTheory.MixModel.rat_mul, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Split

theorem mt_unitary (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.gA V := by
  rw [Matrix.mul_assoc]
  exact GlobalTheory.MixModel.mt_unitary V a

theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  rw [GlobalTheory.MixModel.actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.mul_one]

private lemma rat_adj_mul_gram_eq (V : HSp D) {s : ℕ} (B : Matrix (Fin V.rank) (Fin s) D.host.E) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) = GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
  rw [GlobalTheory.MixModel.rat_mul, adj_rat, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig, GlobalTheory.MixModel.gA]

private lemma gA_mul_mt_eq_adj_mt_inv_mul (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
  calc GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a
      = (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a⁻¹) * Formalism.L2.Theta.mt V a := by
        rw [mt_unitary]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * (Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a) := by
        rw [Matrix.mul_assoc]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
        rw [← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem form_fix (V : HSp D) {s : ℕ} (a : GA D V) (B : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.rat (adj D B * V.gram) := by
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv]

theorem form_scale (V : HSp D) {s : ℕ} (a : GA D V) (C : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C) :
    GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      incA D (1 / 2) • GlobalTheory.MixModel.rat (adj D C * V.gram) := by
  have h2 : incA D (1 / 2) * (2 : AE D) = 1 := by
    rw [← map_ofNat (incA D) 2, ← map_mul]
    norm_num
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
    calc Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C
        = (incA D (1 / 2) * (2 : AE D)) • (Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C) := by rw [h2, one_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * ((2 : AE D) • GlobalTheory.MixModel.rat C)) := by
        rw [mul_smul, Matrix.mul_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C)) := by rw [h]
      _ = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
        rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  have hc : cA D (incA D (1 / 2)) = incA D (1 / 2) := GlobalTheory.MixModel.cA_half
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv,
    GlobalTheory.MixModel.adj_smul, hc, Matrix.smul_mul]

theorem res_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hcov
  refine ⟨1, fun f hf => ?_⟩
  have hC' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C := haC
  have hB' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := haB
  have hsub : ∀ w : WO V W,
      ω (a, 1) f w = f (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a)) := by
    intro w
    have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω a haQ 1 (one_mem _) f hf
      (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a))
    rwa [actO_mul_mt] at h1
  have hiso : ∀ y : Mx D W.rank r,
      HMul.hMul (isoPart V W C y : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
        isoPart V W C (incA D (1 / 2) • y) := by
    intro y
    show y * GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      (incA D (1 / 2) • y) * GlobalTheory.MixModel.rat (adj D C * V.gram)
    rw [Matrix.mul_assoc, form_scale V a C hC', Matrix.mul_smul, Matrix.smul_mul]
  rw [one_smul]
  funext x
  have hmid : HMul.hMul (midPart V V' W B x : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
      midPart V V' W B x := by
    show (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) * Formalism.L2.Theta.mt V a =
      (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram)
    rw [Matrix.mul_assoc V'.gram⁻¹ (adj D B) V.gram, GlobalTheory.MixModel.rat_mul]
    simp only [Matrix.mul_assoc]
    rw [form_fix V a B hB']
  calc res V V' W C B μ 𝓨 (ω (a, 1) f) x
      = ∫ y in 𝓨, f (isoPart V W C (incA D (1 / 2) • y) + midPart V V' W B x) ∂μ := by
        show ∫ y in 𝓨, ω (a, 1) f (isoPart V W C y + midPart V V' W B x) ∂μ = _
        congr 1
        funext y
        rw [hsub, Matrix.add_mul, hiso, hmid]
    _ = ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ :=
        GlobalTheory.UnipMean.mean_smul hcov (c := 1 / 2) (by norm_num)
          (fun y => f (isoPart V W C y + midPart V V' W B x)) (periodic hs hf x)
    _ = res V V' W C B μ 𝓨 f x := rfl

end GlobalTheory.LeviRes
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∃ d : GlobalTheory.MixModel.HypDec V V' r, d.e = C ∧ d.i₀ = B ∧ ∀ m : GA D V, HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = C.map (incA D) → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = B.map (incA D) → m ∈ NI V C := by
  first | exact @GlobalTheory.WittSect.exists_hypDec_mem_NI | exact GlobalTheory.WittSect.exists_hypDec_mem_NI | (intros; apply GlobalTheory.WittSect.exists_hypDec_mem_NI <;> assumption)
end

section

namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_complexSide_of_hilbert_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  first | exact @GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | exact GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 | (intros; apply GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models.rowTest_toCx3 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D := by
  first | exact @GlobalTheory.RationalIsometry.rationalSt | exact GlobalTheory.RationalIsometry.rationalSt | (intros; apply GlobalTheory.RationalIsometry.rationalSt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heckeChar_unramified_above_place_of_trivial_units : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  first | exact @GlobalTheory.UnrOverPlace.unrAt_of_unramAt | exact GlobalTheory.UnrOverPlace.unrAt_of_unramAt | (intros; apply GlobalTheory.UnrOverPlace.unrAt_of_unramAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecGL w ρ x B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | exact GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | (intros; apply GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv <;> assumption)
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  first | exact @GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | exact GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | (intros; apply GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span <;> assumption)
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  first | exact @GlobalTheory.WeightUnfold.exists_weight | exact GlobalTheory.WeightUnfold.exists_weight | (intros; apply GlobalTheory.WeightUnfold.exists_weight <;> assumption)
end
