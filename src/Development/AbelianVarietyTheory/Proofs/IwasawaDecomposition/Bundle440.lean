module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle424
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
public import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle426
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_levelGroup_with_character_at_type_places : ∀ (D : D7) (T : TwR D.LL0 D.nd) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ)
    (QP DP : Finset (PlE D.host)) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)),
    (∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (P' ∈ QP ∨ P' ∈ DP ∨ ∃ kv, P' = NX.pG D kv) →
      (sp P).v = (sp P').v → P = P') →
    (∀ P ∈ QP, P ∉ DP) → (∀ kv, NX.pG D kv ∉ QP ∧ NX.pG D kv ∉ DP) → (∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv') →
    QP ⊆ Q → DP ⊆ T.pD i →
    (∀ P ∈ QP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal ψ P 1 (u * u') = NX.tameVal ψ P 1 u * NX.tameVal ψ P 1 u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal ψ P 1 u = NX.tameVal ψ P 1 u') →
    (∀ P ∈ DP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) (u * u') =
          NX.tameVal (T.delta i) P (if b then 1 else -1) u * NX.tameVal (T.delta i) P (if b then 1 else -1) u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) u = NX.tameVal (T.delta i) P (if b then 1 else -1) u') →
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* (FractionRing (T.Ok i k))ˣ),
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      NX.HypOutsideF J χ (badVT D T i Q) ∧
      (∀ κ : GAf D.host.E D.R.nV, κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV ∧
        (∀ kv, NX.InLevG (sp (NX.pG D kv)).v D.R.r (NX.locM (sp (NX.pG D kv)) κ)) ∧
        (∀ P ∈ QP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ)) ∧
        (∀ P ∈ DP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ))) ∧
      ∀ κ (h : κ ∈ J), ((χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ)) *
        (∏ P ∈ QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) *
        (∏ P ∈ DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
          (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) := by
  first | exact @GlobalTheory.LevGChar.levGroup_exists | exact GlobalTheory.LevGChar.levGroup_exists | (intros; apply GlobalTheory.LevGChar.levGroup_exists <;> assumption)
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

theorem blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin q) (Fin q) ℂ) :
    (fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b =
      fromBlocks (aᴴ * S.toBlocks₁₁ * a) (aᴴ * S.toBlocks₁₂ * b) (bᴴ * S.toBlocks₂₁ * a) (bᴴ * S.toBlocks₂₂ * b) := by
  conv_lhs => rw [← fromBlocks_toBlocks S]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem schur_blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    {b : Matrix (Fin q) (Fin q) ℂ} (hb : IsUnit b.det) :
    schur ((fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b) = aᴴ * schur S * a := by
  have hb' : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact hb.star
  rw [blockDiag_conj, schur, schur]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  rw [mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']

theorem reindex_conj_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (A : Matrix (Fin r) (Fin r) ℂ)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (fromBlocks (uni w.2.2) 0 0 (uni w.2.1))ᴴ * shear (reindex e e A) (toMat w.1) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
  have h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) =
      (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
    simp [fromBlocks_multiply]
  rw [h1, reindex_uni_glue he, h2, shear]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  intro r p q e he A w hS
  have hR := reindex_conj_glue he A w
  set S := shear (reindex e e A) (toMat w.1) with hSdef
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2 := by
    rw [hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]
  obtain ⟨m1, m2⟩ := GlobalTheory.T.leadingMinor_blockDecomposition r p q e he H (hd ▸ hS)
  rw [hd, hs] at m2
  rw [h22] at m1
  unfold dens
  rw [← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]
  have a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc =
      lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc := fun a => m1 _ _ (by simp [he.2])
  have a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc =
      S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc := fun a => m2 _ _ (by simp [he.1])
  simp only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← zpow_natCast, ← _root_.zpow_mul, neg_mul]
  ring

end GlobalTheory.FlagFibre
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.hua_integral_positive_definite_quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  first | exact @GlobalTheory.HuaQuadric.quadric | exact GlobalTheory.HuaQuadric.quadric | (intros; apply GlobalTheory.HuaQuadric.quadric <;> assumption)
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q → ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  first | exact @GlobalTheory.FlagFibre.signs_over_dom | exact GlobalTheory.FlagFibre.signs_over_dom | (intros; apply GlobalTheory.FlagFibre.signs_over_dom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.LamQInv

theorem coarseBlockIndex_single_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem lamQ_castGL_inv : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  intro κ K _ _ a n r b h hn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext; simp [LiftBrg.castGL]
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [b] := by
    intro i j hij
    apply hy
    show Formalism.L2.DIV.blk2 r j < Formalism.L2.DIV.blk2 r i
    rw [← coarseBlockIndex_single_eq_twoBlock hn, ← coarseBlockIndex_single_eq_twoBlock hn]
    exact hij
  have he : (⟨_, hz⟩ : ↥(Formalism.L2.Col.HQ κ a r b)) = (⟨y, hy'⟩ : ↥(Formalism.L2.Col.HQ κ a r b))⁻¹ := by
    ext1
    simp [hc]
  rw [he, map_inv, Formalism.L2.Col.lamQ_apply]
  congr 2
  ext
  rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
  rw [Matrix.toSquareBlock_def]
  let e : {i : Fin a // Formalism.L2.Col.coarse r [b] i.val = 1} ≃ {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} :=
    Equiv.subtypeEquivRight (fun i => by rw [coarseBlockIndex_single_eq_twoBlock hn])
  exact Matrix.det_submatrix_equiv_self e (((y : GL (Fin a) κ) : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} → Fin a) Subtype.val)

end GlobalTheory.Mem.R3.LiftBrg.LamQInv
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg.LamKV

theorem coarse_single_eq_blkOf {a r t : ℕ} (hn : a = r + t) (i : Fin a) :
    Formalism.L2.Col.coarse r [t] i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have h1 : i.val - r < t := by omega
    have h2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt h1
    rw [h2]
    simp [Formalism.L2.Col.blkIdx, h1]

theorem lamKV_inv_mul_diagEmb : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t),
    Formalism.L2.Col.lamKV χ n r t ⟨_, hz⟩ = χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y) := by
  intro κ K _ _ a n r t h hn hra hrn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext i j
    simp [LiftBrg.castGL]
  have hf : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) = Formalism.L2.DIV.blkOf r t :=
    funext (coarse_single_eq_blkOf hn)
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [t] := by
    intro i j hij
    apply hy
    have hij' : (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) j < (fun i : Fin a => Formalism.L2.Col.coarse r [t] i.val) i := hij
    rw [hf] at hij'
    exact hij'
  let Y : Formalism.L2.Col.blockUT a κ r [t] := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT a κ r [t] :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn [t] (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hzz : (Subgroup.inclusion (Formalism.L2.Col.HK_le_blockUT a κ r [t]) ⟨_, hz⟩ : Formalism.L2.Col.blockUT a κ r [t]) = Y⁻¹ * Dd := by
    apply Subtype.ext
    show (LiftBrg.castGL (rfl : a = a) y)⁻¹ * _ = y⁻¹ * _
    rw [hc]
  have hD : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Dd = 1 := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Units.val_one]
    have : (Dd.1 : Matrix (Fin a) (Fin a) κ).toSquareBlock (fun i => Formalism.L2.Col.coarse r [t] i.val) 1 = 1 := by
      ext i j
      have hi : ¬ i.1.val < r := fun hi => by
        have := i.2
        simp only [Formalism.L2.Col.coarse_of_lt hi] at this
        exact absurd this (by decide)
      rw [Matrix.toSquareBlock_def, Matrix.of_apply]
      show Formalism.L2.Col.diagMat r a _ i.1 j.1 = _
      rw [Formalism.L2.Col.diagMat_of_not_left _ _ hi]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hY : Formalism.L2.Col.blkDet a κ (Formalism.L2.Col.coarse r [t]) 1 Y = Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y := by
    apply Units.ext
    rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
    have key : ∀ b : Fin a → ℕ, b = Formalism.L2.DIV.blkOf r t →
        ((y : Matrix (Fin a) (Fin a) κ).toSquareBlock b 1).det =
          ((y : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {x : Fin a // Formalism.L2.DIV.blkOf r t x = 1} → Fin a)
            Subtype.val).det := by
      rintro b rfl
      rfl
    exact key _ hf
  rw [Formalism.L2.Col.lamKV, Formalism.L2.Col.lamK, MonoidHom.comp_apply, hzz, Formalism.L2.Col.detChar_apply]
  simp only [List.length_singleton, Finset.range_one, Finset.prod_singleton, zero_add]
  rw [map_mul, map_inv, hD, mul_one, hY, MonoidHom.inv_apply, map_inv, inv_inv]

end GlobalTheory.Mem.R3.LiftBrg.LamKV
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_mem_UA_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {m n : ℕ} (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E) ↔
      x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin m) (Fin m) E) := by
  subst h
  have : castGL (rfl : m = m) x = x := by
    ext i j
    rfl
  rw [this]

theorem frameOK_one_of_gram_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (i : Fin X.toD7.R.m) (t : TupU I U) (hg : (Vc X.toD7 i).gram = 1) : LiftBrg.FrameOK X I U i t 1 1 := by
  refine ⟨⟨1, (map_one _).symm⟩, one_mem _, fun x => ?_, one_mem _, one_mem _, fun PP _ => ?_⟩
  · rw [hg, one_mul, inv_one, mul_one]
    exact (castGL_mem_UA_one X.toD7.sp.cm (rkEq X i) x).symm
  · rw [one_mul]; exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

variable (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
  (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))

theorem mem_parLev_of_Q (i : Fin X.toD7.R.m) (t : TupU I U) (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := q.2.1

def rV (i : Fin X.toD7.R.m) (t : TupU I U) (x : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)) : G0 L.Pg X.toD7.R.r :=
  rTup (L.βV i) (L.datVt i t) x

theorem rV_one (i : Fin X.toD7.R.m) (t : TupU I U) : rV X I U L i t 1 = 1 := rTup_one

theorem rV_mul (i : Fin X.toD7.R.m) (t : TupU I U) {x y : GL (Fin (Vc X.toD7 i).rank) (Formalism.IndefR.Lev.EAf X.toD7)}
    (hx : x ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t))
    (hy : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t)) :
    rV X I U L i t (x * y) = rV X I U L i t x * rV X I U L i t y := rTup_mul hx hy

def redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U) :
    (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q →* Gc X.B px where
  toFun q := eG.symm (rV X I U L i t
    (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [rV_one, map_one]
  map_mul' a b := by
    simp only [Subgroup.coe_mul, map_mul]
    rw [rV_mul X I U L i t (mem_parLev_of_Q X I U L i t a) (mem_parLev_of_Q X I U L i t b), map_mul]

theorem redQ_apply (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = eG.symm (rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := rfl

theorem eG_redQ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    eG (redQ X I U L eG i t q) = rV X I U L i t
      (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) := by
  rw [redQ_apply]
  exact eG.apply_symm_apply _

theorem redQ_eq_one_iff (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (i : Fin X.toD7.R.m) (t : TupU I U)
    (q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    redQ X I U L eG i t q = 1 ↔ (q : Bridge.Gf (Vc X.toD7 i)) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := by
  rw [redQ_apply, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact ⟨mem_parLev_of_Q X I U L i t q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

def ptS (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet (E := X.B.fields.E) (n := X.B.R.nV) (ST := ∅) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  ptL X I U i t A k g

def redZ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) :
    Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :=
  fun w => Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  first | exact @GlobalTheory.GenHypOut.genHyp | exact GlobalTheory.GenHypOut.genHyp | (intros; apply GlobalTheory.GenHypOut.genHyp <;> assumption)
end

section

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.conjugate_evaluation_intertwiner_cuspidal_values : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  exact @GlobalTheory.ConjRowCuspGap.conjMap_isCuspFun
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  first | exact @GlobalTheory.Mem.Col2.Splice.isPtOf_splice | exact GlobalTheory.Mem.Col2.Splice.isPtOf_splice | (intros; apply GlobalTheory.Mem.Col2.Splice.isPtOf_splice <;> assumption)
end
