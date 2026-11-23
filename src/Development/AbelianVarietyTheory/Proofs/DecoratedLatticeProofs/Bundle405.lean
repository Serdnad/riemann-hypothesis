module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle448
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle380
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle368
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceAtG

theorem mat_embA_besFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) (h : GA D B.A)
    (g₀ : GL n k) (hh : (mt B.A h).map p.π = FA.β * g₀.val * FA.γ) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (GlobalTheory.RootEx.embX c g₀).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  have hint : (mt B.V (B.d.emb0 (B.o.emb (h, 1)))).map p.π * ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) =
      (rat (B.d.i₀ * B.o.iA)).map p.π * FA.β * g₀.val := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, eA, Matrix.map_mul, hh]
    simp only [Matrix.mul_assoc]
    rw [FA.γβ, Matrix.mul_one]
  refine GlobalTheory.LocGrp.eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 hint fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.TraceAtG

end

noncomputable section
open GlobalTheory.FamTrace

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hgtL_eq_conj_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  intro D A L L' hL hL'
  obtain ⟨k, hk, hK⟩ := GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact D A L L' hL hL'
  refine ⟨k, hk, fun a ha g => ?_⟩
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L hL
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L' hL'
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L' a hL' ha
  have hj : io A (k, k) ∈ siegel A := (io_mem_siegel A).2 rfl
  obtain ⟨p, κ, hκ, hx⟩ := hI (io A (g, 1))
  have hκ' : (io A (k, k))⁻¹ * κ * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := (hK a κ).1 hκ
  have e : io A (k⁻¹ * g * k, 1) =
      ((⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) : GA D (dblSp A)) *
        ((io A (k, k))⁻¹ * κ * io A (k, k)) := by
    have h1 : io A (k⁻¹ * g * k, 1) = (io A (k, k))⁻¹ * io A (g, 1) * io A (k, k) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      simp
    rw [h1, hx]
    simp [mul_assoc]
  change hgtAd _ _ L' a (io A (g, 1)) = hgtAd _ _ L a (io A (k⁻¹ * g * k, 1))
  rw [hx, e]
  calc
    hgtAd _ _ L' a (↑p * κ) = _ := hgtAd_mul (isCMExt_host D) p hκ
    _ = _ := by
      congr 1
      rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    _ = hgtAd _ _ L a (↑(⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) *
        ((io A (k, k))⁻¹ * κ * io A (k, k))) :=
      (hgtAd_mul (isCMExt_host D) _ hκ').symm

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.LevMoves

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    M *ᵥ (fun i => q.sec (y i)) = fun i => q.sec ((M.map q.pr *ᵥ y) i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := q.sec_pr (M i j * q.sec (y j))
  rw [RingHom.map_mul, q.pr_sec, mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem isLat_moved (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (S : HSp D)
    (Λ L : Lat S) (β : GL (Fin S.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (t : GA D S)
    (ht : Moves S t Λ L (· = q.v)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (bas : GL Y k)
    (σ : Fin S.rank ≃ Y) (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β ((F.β * bas.val).submatrix id σ))
    (x : Y → k) : x ∈ GlobalTheory.StepData.latOf bas ↔ (fun i => q.sec ((F.β *ᵥ x) i)) ∈ latV S L (· = q.v) := by
  obtain ⟨B, hB, hl⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame q hq S Λ β hβ
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  have h1 := hB _ e
  have h2 := hM _ e
  rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul] at h1
  rw [Matrix.map_mul, h1] at h2
  have h3 : (mt S t).map q.pr *ᵥ (B.val *ᵥ fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = F.β *ᵥ x := by
    rw [Matrix.mulVec_mulVec]
    refine (congrArg (· *ᵥ _) h2).trans ?_
    have : (fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = ((bas⁻¹).val *ᵥ x) ∘ σ := rfl
    rw [this, Matrix.submatrix_mulVec_equiv, Function.comp_id, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← h3, ← mulVec_sec, ← ht _ fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _, hl, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec, GlobalTheory.StepData.mem_latOf]
  exact ⟨fun h i => h _, fun h i => by simpa using h (σ.symm i)⟩

theorem smul_latOf {Y : Type} [Fintype Y] [DecidableEq Y] {bas g : GL Y k} (h : g ∈ GlobalTheory.StepData.stabLat bas) :
    g • GlobalTheory.StepData.latOf bas = GlobalTheory.StepData.latOf bas := by
  have h1 := GlobalTheory.StepData.mem_stabLat_iff.1 h
  ext y
  conv_rhs => rw [← h1]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf bas ∧ g • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf g).2 hx
  · intro hy
    refine ⟨g⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf g).1 ?_, smul_inv_smul _ _⟩
    have : g.val *ᵥ (g⁻¹ • y) = y := smul_inv_smul g y
    rwa [this]

end

end GlobalTheory.SeeSaw.LevMoves
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocModMove

theorem placeIdem_mul_eq_zero {D : D7} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε) (a : AE D)
    (ha : a ∈ GlobalTheory.FinPl.idOff D (· = v)) : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := GlobalTheory.FinPl.placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hav : GlobalTheory.FinPl.compAt D v a = 0 := by
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha
    exact ha v rfl
  apply GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · subst h; rw [hav, mul_zero]
    · rw [hc w, hw w h, TensorProduct.zero_tmul, zero_mul]

theorem ent_of_mem_grpOff {D : D7} {V : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V P) :
    ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D P := by
  have hker := MonoidHom.mem_ker.1 hg
  intro i j
  rw [← Ideal.Quotient.eq]
  have h2 := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P) => u.1 i j) hker
  simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
  have h3 : Ideal.Quotient.mk (GlobalTheory.FinPl.idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ GlobalTheory.FinPl.idOff D P)) i j := by
    by_cases hij : i = j
    · subst hij; simp only [Matrix.one_apply_eq, map_one]
    · simp only [Matrix.one_apply_ne hij, map_zero]
  rw [h3, ← h2]
  rfl

theorem mul_mul_eq_self {D : D7} {m n : ℕ} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (A : Matrix (Fin m) (Fin m) (AE D)) (B : Matrix (Fin n) (Fin n) (AE D)) (y : Matrix (Fin m) (Fin n) (AE D))
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hB : ∀ i j, B i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j ∈ GlobalTheory.FinPl.idOff D (· = v))
    (hy : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * y i j = y i j) : HMul.hMul (HMul.hMul A y) B = y := by
  have kill : ∀ a ∈ GlobalTheory.FinPl.idOff D (· = v), ∀ b : AE D, b = algebraMap (AF D.host.F) (AE D) ε * b → a * b = 0 := by
    intro a ha b hb
    rw [hb, ← mul_assoc, mul_comm a, placeIdem_mul_eq_zero v ε hε a ha, zero_mul]
  have h1 : HMul.hMul (A - 1) y = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply]
    exact kill _ (hA i l) _ (hy l j).symm
  have h2 : HMul.hMul y (B - 1) = (0 : Matrix (Fin m) (Fin n) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.sub_apply, mul_comm]
    exact kill _ (hB l j) _ (hy i l).symm
  have e1 : HMul.hMul A y = y := by
    rw [← sub_eq_zero, ← h1, Matrix.sub_mul, Matrix.one_mul]
  have e2 : HMul.hMul y B = y := by
    rw [← sub_eq_zero, ← h2, Matrix.mul_sub, Matrix.mul_one]
  rw [e1, e2]

theorem actO_eq_self {D : D7} {V W : HSp D} (v : GlobalTheory.FinPl.Pl D) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = v)) {h : GA D W} (hh : h ∈ GlobalTheory.FinPl.grpOff W (· = v))
    (y : WO V W) (hy : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y) : actO V W g h y = y := by
  unfold actO
  exact mul_mul_eq_self v ε hε _ _ _ (ent_of_mem_grpOff hh)
    (ent_of_mem_grpOff ((GlobalTheory.FinPl.grpOff V (· = v)).inv_mem hg)) hy

theorem isModel_weil_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  intro D k _ _ _ _ q ψ hψ V W χV χW ω hω Y Y' _ _ _ _ FV FW Tm hM g hg h hh
  obtain ⟨ε, hεv, hsum⟩ := q.above
  refine (GlobalTheory.LocModU.localModel_uniq_transport_exist D k (ofSplit q) Y Y' V W FV FW ψ hψ).2.1 Tm hM (ω (g, h))
    (fun f hf => hω.om_pres _ f hf) (fun f hf y hy => ?_)
  have hy' : IsHalf (algebraMap (AF D.host.F) (AE D) ε) y := by
    rw [← hsum]; exact hy
  rw [hω.om_heis g h y f hf, actO_eq_self q.v ε hεv hg hh y hy']

end GlobalTheory.LocModMove
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  first | exact @GlobalTheory.BiComb.comb_bimodel_and_line | exact GlobalTheory.BiComb.comb_bimodel_and_line | (intros; apply GlobalTheory.BiComb.comb_bimodel_and_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.support_levelPlace_symmetricChain_secondHalf : ∀ (D : D7), OmLoc D → FlatBF D → FlatFB D → ContrLoc D → GlobalTheory.LocFlat.SymCollapse →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.IsChar ψ S.ψ → ∀ (j c : ℕ) (H : j + 1 + 1 + c = s) (σ : ℕ) (B : BesLev D (σ + 1))
    (J : JacLev D (σ + 1)) (B' : BesLev D σ) (F : Dbl p B J B' (GlobalTheory.StepData.XIx (Fin κ) t j) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1)) (GlobalTheory.StepData.XIx (Fin κ) t (j + 1 + 1)) c)
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank),
    p.IsComp s₂.χV⁻¹ (S.μ (j + 1 + 1)) →
  ∀ T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂, Φ₁.1 = (S.T t).Phi j (c + 1 + 1) (by omega) →
    Φ₂.1 = (S.T t).Phi (j + 1) (c + 1) (by omega) →
  ∀ h, SuppAt p.e B'.V h → GlobalTheory.Unf.contr l J.W₀ vL (flatBF s₁ (T₁ Φ₁)) (flatFB s₂ (s₂.om (1, h) (T₂ Φ₂))) ≠ 0 →
    ∃ r ∈ besGrp B'.d B'.o, SuppAt p.e B'.V r ∧
      ∃ u uk, p.IsLoc F.G₂ u uk ∧ uk ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J ∧ h = r * u := by
  first | exact @GlobalTheory.LocMod.GSuppTwo.gsupp2_std | exact GlobalTheory.LocMod.GSuppTwo.gsupp2_std | (intros; apply GlobalTheory.LocMod.GSuppTwo.gsupp2_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.flat_map_support_first_half_at_level_place : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  first | exact @GlobalTheory.LocMod.SuppFirst.gsupp1 | exact GlobalTheory.LocMod.SuppFirst.gsupp1 | (intros; apply GlobalTheory.LocMod.SuppFirst.gsupp1 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (gl : GL Y k →* GA D V), (∀ g, (ofSplit q).IsLoc F (gl g) g) → Topology.IsClosedEmbedding gl ∧ gl.range = GlobalTheory.FinPl.grpAt V (· = q.v) ∧ (∀ x : GA D V, ∃! g, x * (gl g)⁻¹ ∈ GlobalTheory.FinPl.grpOff V (· = q.v)) ∧ (∀ g, ∀ y ∈ GlobalTheory.FinPl.grpOff V (· = q.v), gl g * y = y * gl g) ∧ ∀ L : GlobalTheory.FinPl.Lat V, IsSelfDualC V L → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV V L (· = q.v)) → ∀ g, g ∈ KO k Y ↔ GlobalTheory.FinPl.InK V L (· = q.v) (gl g) := by
  first | exact @GlobalTheory.LocGl.local_group | exact GlobalTheory.LocGl.local_group | (intros; apply GlobalTheory.LocGl.local_group <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  first | exact @GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | exact GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | (intros; apply GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw.TwLaw
variable {D : D7}

theorem levChi_flag (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    Lev.levChi V β (Lev.flagL (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) κ =
      Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) κ := by
  unfold Lev.levChi levFn
  congr 3
  simp only [Lev.flagL, Lev.withP, Lev.datY, LevelP.full, LevelP.triv, if_true]
  exact (Lev.subgroupCharExtension_one_apply _ _).trans (Lev.subgroupCharExtension_one_apply _ _).symm

theorem lift_one_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) (hκ : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) :
    Lev.IsLevelLift V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) 1 κ := by
  refine ⟨(Subgroup.mem_inf.1 hκ).1, hκ.2.1, ?_⟩
  have h2 := hκ.2.2
  simp only [Lev.datY, LevelP.triv, if_true] at h2
  exact Subgroup.mem_bot.1 h2

theorem lift_one_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β L 1 = 1 := by
  unfold Lev.levChi
  rw [map_one]
  have : levFn β L 1 = 1 := (levChar D.sp.cm V.gram β L).map_one
  rw [this, Units.val_one]



open Classical in
theorem vecLawQ (D : D7) (c : Com D) (w : Twist D) (hw : w.Is c) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D)
    (hs : IsStage c w k s) (hs' : IsStage c w (k + 1) s') (p : Step c s s') (hp : IsStep w (k + 1) p) :
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  obtain ⟨hr, hL, hfs⟩ := hs
  obtain ⟨hr', hL', hfs'⟩ := hs'
  obtain ⟨f₀, hv⟩ := hp.vec
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  rw [hw.union] at hres uS uT
  have hG : ∀ PP ∈ w.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.chi (k + 1) PP)⁻¹ ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.chi (k + 1) PP)⁻¹ := fun PP hP => by
    rw [← hw.chiPg (k + 1) PP hP]; exact hres PP (Finset.mem_union_left _ hP)
  have hQ : ∀ PP ∈ w.Q, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.ξ PP) ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.ξ PP) := fun PP hP => by
    have := hres PP (Finset.mem_union_right _ hP)
    rwa [hw.chiQ (k + 1) PP hP, inv_inv] at this
  rw [hL] at hv
  have ea : s.V.rank = D.R.r + k * D.R.t := hfs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hfs'.rank
  have law := fun {g0 : G0 w.Pg D.R.r} {g : GA D s.V} {h : GA D s'.V} =>
    @GlobalTheory.StepVecLaw.step_law D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β f₀ p.f
      hp.weil hfs.sigOK hfs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
      hfs.selfDual hfs'.selfDual hfs.frame hfs'.frame D.R.r D.R.t k hr hr' ea eb w.Pg w.Q hw.disj w.chi w.ξ hv hG hQ uS uT g0 g h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · rw [hL] at hκ ⊢
    have h1 := law (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ) (lift_one_one _ _ _)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    have hne : Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t k hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) κ ≠ 0 := by
      unfold Lev.levChi; exact Units.ne_zero _
    exact (inv_smul_eq_iff₀ hne).1 h1
  · rw [hL'] at hκ ⊢
    have h1 := law (lift_one_one _ _ _) (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    exact h1

theorem levelLawQ : ∀ D : D7, LevelLawQ D := by
  intro D _ c w hw k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := vecLawQ D c w hw k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainTw.TwLaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  first | exact @GlobalTheory.ChainTw.fock_sph_tw | exact GlobalTheory.ChainTw.fock_sph_tw | (intros; apply GlobalTheory.ChainTw.fock_sph_tw <;> assumption)
end
