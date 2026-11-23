module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle338
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle340
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerPCpt

theorem pure_add' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.add_apply, Pi.add_apply, add_mul]

theorem pure_smul' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem pure_zero' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) φ = 0 := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.zero_apply, Pi.zero_apply, zero_mul]

theorem pure_sub' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.sub_apply, sub_mul]

theorem isHecke_quot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  unfold GlobalTheory.LFun.IsHecke at h h' ⊢
  obtain ⟨hc, hx⟩ := h
  obtain ⟨hc', hx'⟩ := h'
  refine ⟨?_, fun x => ?_⟩
  · have hfun : (⇑(χ / χ')) = fun z => χ z / χ' z := funext (MonoidHom.div_apply χ χ')
    rw [hfun]
    exact hc.div' hc'
  · rw [MonoidHom.div_apply, hx x, hx' x, div_one]

theorem resEtaPow_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) (hk : k = n + m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') k := by
  unfold GlobalTheory.WeilM.ResEtaPow at h h' ⊢
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u, hk]
  split_ifs
  · norm_num
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

theorem isPair_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_quot h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_quot h.chars.resα h.chars.resβ (by omega)
    weil := h.weil' }

end GlobalTheory.SquareAgree.KerPCpt

namespace GlobalTheory.SquareAgree.KerPCpt

end GlobalTheory.SquareAgree.KerPCpt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.rank_schwartzBruhat_adicCompletion_pi_le_aleph0 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | exact GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | (intros; apply GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section
namespace GlobalTheory.BlockSubstFourier

theorem invFourierSum_comp_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) (hΦ : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ)
    (M₁ : GL D₁ k) (hM₁ : M₁ ∈ KO k D₁) (M₂ : GL D₂ k) (hM₂ : M₂ ∈ KO k D₂) (X : Matrix A (D₁ ⊕ D₂) k) :
    invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [compl_block_one] at hΦ ⊢
  set P := Assignment.two.block D₁ D₂ with hP
  have inr_mem : ∀ j : D₂, (Sum.inr j : D₁ ⊕ D₂) ∈ P := fun j => by simp [hP, Assignment.block]
  have inl_nmem : ∀ j : D₁, (Sum.inl j : D₁ ⊕ D₂) ∉ P := fun j => by simp [hP, Assignment.block]
  let eP : D₂ ≃ P := Equiv.ofBijective (fun j => ⟨Sum.inr j, inr_mem j⟩) ⟨fun a b h => by simpa using h, by
    rintro ⟨(j | j), h⟩
    · exact absurd h (inl_nmem j)
    · exact ⟨j, rfl⟩⟩
  have eP_apply : ∀ j, (eP j : D₁ ⊕ D₂) = Sum.inr j := fun j => rfl
  set M := fromBlocks M₁.val 0 0 M₂.val with hM
  set M' := fromBlocks M₁.val 0 0 (invT M₂).val with hM'
  set Nk : Matrix P P k := (invT M₂).val.submatrix eP.symm eP.symm with hNk
  have hNk_apply : ∀ a b, Nk (eP a) (eP b) = (invT M₂).val a b := fun a b => by simp [hNk]
  obtain ⟨u, hu⟩ := invT_mem_KO hM₂
  let N : Matrix P P 𝒪[k] := u.val.submatrix eP.symm eP.symm
  let N' : Matrix P P 𝒪[k] := (u⁻¹).val.submatrix eP.symm eP.symm
  have hNN : N * N' = 1 := by
    simp only [N, N', Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hNmap : N.map (fun x => (x : k)) = Nk := by
    rw [hNk, ← hu]; ext i j; rfl
  have hM₂i := (mem_KO_iff M₂).1 hM₂

  set X₂ : Matrix A D₂ k := X.submatrix id Sum.inr with hX₂
  have hXM₂ : (X * M).submatrix id Sum.inr = X₂ * M₂.val := by
    ext i j; simp [hM, hX₂, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have condP : ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ P, Z i j ∈ 𝒪[k]) ↔ ∀ i (j : D₂), Z i (Sum.inr j) ∈ 𝒪[k] := by
    intro Z
    refine forall_congr' fun i => ⟨fun h j => h _ (inr_mem j), fun h j hj => ?_⟩
    rcases j with j | j
    · exact absurd hj (inl_nmem j)
    · exact h j
  have hsum : ∀ (T : Matrix A P k) (Y : Matrix A (D₁ ⊕ D₂) k),
      pairCols P Y T = trace (T.submatrix id eP * (Y.submatrix id Sum.inr)ᵀ) := by
    intro T Y
    simp only [pairCols, trace, Matrix.mul_apply, diag_apply, transpose_apply, submatrix_apply, id]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Equiv.sum_comp eP (fun j => T i j * Y i j)).symm
  have hTN : ∀ T : Matrix A P k, (T * Nk).submatrix id eP = T.submatrix id eP * (invT M₂).val := by
    intro T; ext i j
    simp only [submatrix_apply, id, Matrix.mul_apply]
    rw [← Equiv.sum_comp eP]
    simp [hNk_apply]
  have hset : ∀ T : Matrix A P k, setCols P X T * M' = setCols P (X * M) (T * Nk) := by
    intro T; ext i (j | j)
    · simp [hM, hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
    · have h1 : setCols P (X * M) (T * Nk) i (Sum.inr j) = (T.submatrix id eP * (invT M₂).val) i j := by
        rw [← hTN]; simp only [setCols, Matrix.of_apply, dif_pos (inr_mem j), submatrix_apply, id]; rfl
      rw [h1]
      simp [hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
      rfl
  have hpair : ∀ T : Matrix A P k, pairCols P (X * M) (T * Nk) = pairCols P X T := by
    intro T
    rw [hsum, hsum, hTN, hXM₂, transpose_mul, invT_val]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ M₂.valᵀ, ← transpose_mul, Units.mul_inv, transpose_one,
      Matrix.one_mul]
  have setCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      setCols P Y (T + T') = setCols P Y T + setCols P 0 T' := by
    intro Y T T'; ext i j
    by_cases h : j ∈ P <;> simp [setCols, h]
  have pairCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      pairCols P Y (T + T') = pairCols P Y T + pairCols P Y T' := by
    intro Y T T'; simp [pairCols, add_mul, Finset.sum_add_distrib]
  have hcZ : ∀ z : k, valuation k z ≤ valuation k ((ϖ ^ e : kˣ) : k) → (((ϖ ^ e)⁻¹ : kˣ) : k) * z ∈ 𝒪[k] := by
    intro z hz
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
    exact hz
  rw [invFourierSum_apply, invFourierSum_apply]
  by_cases hX : ∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]
  · have hXM : ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      rw [condP] at hX ⊢
      intro i j
      have := congrFun (congrFun hXM₂ i) j
      simp only [submatrix_apply, id] at this
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (hX i l) (hM₂i.1 l j)
    rw [if_pos hX, if_pos hXM]
    let F : Matrix A P k → ℂ := fun T =>
      Φ (setCols P (X * M) ((ϖ ^ e)⁻¹ • T)) * (ψ (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • T)) : ℂ)
    have step : ∀ S : A → P → Res k e,
        Φ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S) * M') * (ψ (-pairCols P X ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) =
          F (liftRes S * N.map (fun x => (x : k))) := by
      intro S
      rw [hNmap]
      simp only [F]
      rw [← Matrix.smul_mul, ← hset, hpair]
    have hF : ∀ T Z : Matrix A P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        F (T + Z) = F T := by
      intro T Z hZ
      simp only [F, smul_add, setCols_add', pairCols_add', neg_add, AddChar.map_add_eq_mul]
      have hcZ' : ∀ i j, ((ϖ ^ e)⁻¹ • Z) i j ∈ 𝒪[k] := fun i j => by
        simpa [Units.smul_def] using hcZ _ (hZ i j)
      rw [hΦ.2, triv (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • Z)), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        exact mul_mem (hcZ' i j) (hXM i j j.2)
      · refine FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simpa [setCols, hj] using hcZ' i ⟨j, hj⟩
        · simp [setCols, hj]
    simp only [step]
    exact GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hNN F hF
  · have hXM : ¬ ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      intro h'
      apply hX
      rw [condP] at h' ⊢
      intro i j
      have hX₂ : X₂ = (X * M).submatrix id Sum.inr * (M₂⁻¹).val := by
        rw [hXM₂, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      have : X i (Sum.inr j) = ((X * M).submatrix id Sum.inr * (M₂⁻¹).val) i j := congrFun (congrFun hX₂ i) j
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (h' i l) (hM₂i.2 l j)
    rw [if_neg hX, if_neg hXM]

end GlobalTheory.BlockSubstFourier
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.BlockSubst

def firstCols (D₁ D₂ : Type) [Fintype D₁] [Fintype D₂] : D₁ ≃ ↥(Assignment.one.block D₁ D₂) where
  toFun j := ⟨Sum.inl j, by simp [Assignment.block]⟩
  invFun x := Sum.getLeft x.1 (by simpa [Assignment.block] using x.2)
  left_inv j := rfl
  right_inv x := by
    obtain ⟨x | x, hx⟩ := x
    · rfl
    · simp [Assignment.block] at hx

theorem forall_mem_block_one {D₁ D₂ : Type} [Fintype D₁] [Fintype D₂] (p : D₁ ⊕ D₂ → Prop) :
    (∀ j ∈ Assignment.one.block D₁ D₂, p j) ↔ ∀ j : D₁, p (Sum.inl j) := by
  constructor
  · intro h j; exact h _ (by simp [Assignment.block])
  · rintro h (j | j) hj
    · exact h j
    · simp [Assignment.block] at hj

theorem sum_mul_eq_trace {A D : Type} [Fintype A] [Fintype D] {k : Type} [Field k] (X Z : Matrix A D k) :
    ∑ i, ∑ j, X i j * Z i j = trace (X * Zᵀ) := by
  simp [trace, Matrix.mul_apply]

end GlobalTheory.BlockSubst

open GlobalTheory.BlockSubst in
theorem GlobalTheory.BlockSubst.fourierSum_blockDiag_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ Y : Matrix A (D₁ ⊕ D₂) k,
      fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) Y =
        fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂ Y
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  set P := Assignment.one.block D₁ D₂ with hP
  set E := firstCols D₁ D₂ with hE
  set c : k := ((ϖ ^ e : kˣ) : k) with hc
  obtain ⟨hM1, hM1'⟩ := (mem_KO_iff M₁).1 hM₁
  obtain ⟨hT1, hT1'⟩ := (mem_KO_iff _).1 (invT_mem_KO hM₁)
  have hsumP : ∀ f : ↥P → k, ∑ j : ↥P, f j = ∑ j : D₁, f (E j) := fun f =>
    (Fintype.sum_equiv E _ _ fun _ => rfl).symm
  have hX1 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inl j) = ∑ l, X i (Sum.inl l) * a l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  have hX2 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inr j) = ∑ l, X i (Sum.inr l) * b l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  set Y₁ : Matrix A D₁ k := Matrix.of fun i j => Y i (Sum.inl j) with hY₁
  have hYH : ∀ i j, (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i (Sum.inl j) = (Y₁ * (invT M₁).val) i j := by
    intro i j; rw [hX1]; simp [Y₁, Matrix.mul_apply]
  have hinv : (invT M₁).val * M₁.valᵀ = 1 := by
    rw [invT_val, ← transpose_mul, Units.mul_inv, transpose_one]
  have hinv' : M₁.val * ((invT M₁).val)ᵀ = 1 := by
    rw [invT_val, transpose_transpose, Units.mul_inv]
  have hint : ∀ (X : Matrix A D₁ k) (B : Matrix D₁ D₁ k), (∀ i j, B i j ∈ 𝒪[k]) →
      (∀ i j, c * X i j ∈ 𝒪[k]) → ∀ i j, c * (X * B) i j ∈ 𝒪[k] := by
    intro X B hB hX i j
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Subring.sum_mem _ fun l _ => by rw [← mul_assoc]; exact mul_mem (hX i l) (hB l j)
  have hcond : (∀ i, ∀ j ∈ P, c * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ P, c * (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i j ∈ 𝒪[k]) := by
    simp only [hP, forall_mem_block_one, hYH]
    constructor
    · intro h; exact hint Y₁ _ hT1 h
    · intro h i j
      have := hint _ M₁.valᵀ (fun i j => by simpa using hM1 j i) h i j
      rwa [Matrix.mul_assoc, hinv, Matrix.mul_one] at this
  set YH := Y * fromBlocks (invT M₁).val 0 0 M₂.val with hYHdef
  have hset : ∀ T' : Matrix A ↥P k, setCols P YH (T' * M₁.val.submatrix E.symm E.symm) =
      setCols P Y T' * fromBlocks M₁.val 0 0 M₂.val := by
    intro T'
    ext i (j | j)
    · rw [hX1]
      simp only [setCols, Matrix.of_apply]
      rw [dite_eq_left (by simp [hP, Assignment.block]), Matrix.mul_apply, hsumP]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dite_eq_left (by simp [hP, Assignment.block])]
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      rfl
    · rw [hX2]
      simp only [setCols, Matrix.of_apply]
      rw [dite_eq_right (by simp [hP, Assignment.block]), hYHdef, hX2]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dite_eq_right (by simp [hP, Assignment.block])]
  have hpc : ∀ (Z : Matrix A (D₁ ⊕ D₂) k) (S : Matrix A ↥P k),
      pairCols P Z S = ∑ i, ∑ j : D₁, S i (E j) * Z i (Sum.inl j) := by
    intro Z S; simp only [pairCols]; exact Finset.sum_congr rfl fun i _ => hsumP _
  have hpair : ∀ T' : Matrix A ↥P k, pairCols P YH (T' * M₁.val.submatrix E.symm E.symm) = pairCols P Y T' := by
    intro T'
    set T₁ : Matrix A D₁ k := Matrix.of fun i j => T' i (E j) with hT₁
    have hTN : ∀ i j, (T' * M₁.val.submatrix E.symm E.symm) i (E j) = (T₁ * M₁.val) i j := by
      intro i j; rw [Matrix.mul_apply, hsumP]; simp [T₁, Matrix.mul_apply]
    rw [hpc, hpc]
    simp only [hTN, hYH]
    calc ∑ i, ∑ j, (T₁ * M₁.val) i j * (Y₁ * (invT M₁).val) i j
        = trace ((T₁ * M₁.val) * (Y₁ * (invT M₁).val)ᵀ) := sum_mul_eq_trace _ _
      _ = trace (T₁ * Y₁ᵀ) := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M₁.val, hinv', Matrix.one_mul]
      _ = ∑ i, ∑ j, T' i (E j) * Y i (Sum.inl j) := (sum_mul_eq_trace T₁ Y₁).symm
  rw [fourierSum_apply, fourierSum_apply]
  beta_reduce
  split_ifs with h1 h2 h2
  · congr 1
    obtain ⟨u, hu⟩ := hM₁
    let N : Matrix ↥P ↥P 𝒪[k] := u.val.submatrix E.symm E.symm
    let N' : Matrix ↥P ↥P 𝒪[k] := (u⁻¹).val.submatrix E.symm E.symm
    have hN : N * N' = 1 := by
      simp only [N, N', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
    have hNk : N.map (fun x => (x : k)) = M₁.val.submatrix E.symm E.symm := by
      rw [← hu]; rfl
    have hF : ∀ T Z : Matrix A ↥P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        Φ (setCols P YH (T + Z)) * (ψ (pairCols P YH (T + Z)) : ℂ) =
          Φ (setCols P YH T) * (ψ (pairCols P YH T) : ℂ) := by
      intro T Z hZ
      have e1 : setCols P YH (T + Z) = setCols P YH T + setCols P 0 Z := by
        ext i j; by_cases hj : j ∈ P <;> simp [setCols, hj]
      have e2 : pairCols P YH (T + Z) = pairCols P YH T + pairCols P YH Z := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      rw [e1, e2, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P YH Z), mul_one]
      · refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        have h3 := (Valuation.mem_integer_iff _ _).1 (h2 i j j.2)
        rw [map_mul] at h3
        rw [Valuation.mem_integer_iff, map_mul]
        exact (show valuation k (Z i j) * valuation k (YH i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) * valuation k (YH i j) by
          gcongr; exact hZ i j).trans h3
      · rw [GlobalTheory.SplitFlip.stdLat, smul_diagLat]
        simp only [Pi.one_apply, mul_one]
        change ∀ i j, valuation k (setCols P 0 Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)
        intro i j
        by_cases hj : j ∈ P
        · simpa [setCols, hj] using hZ i ⟨j, hj⟩
        · simp [setCols, hj]
    have key : ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T * N.map (fun x => (x : k)))) *
          (ψ (pairCols P YH (liftRes T * N.map (fun x => (x : k)))) : ℂ) =
        ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T)) * (ψ (pairCols P YH (liftRes T)) : ℂ) :=
      GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hN (fun T' => Φ (setCols P YH T') * (ψ (pairCols P YH T') : ℂ)) hF
    rw [← key, hNk]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hset, hpair]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))),
    ∃ gS k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J, g = gS * k ∧
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) ∧
      (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
        u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1)) ∧
      (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z) := by
  first | exact @GlobalTheory.PlaceCut.exists_cut | exact GlobalTheory.PlaceCut.exists_cut | (intros; apply GlobalTheory.PlaceCut.exists_cut <;> assumption)
end
