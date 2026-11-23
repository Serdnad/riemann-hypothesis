module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle140
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle153
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineProj

open GlobalTheory.IwaPlace

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {π : Mx D S.rank S.rank} (h : adj π ⬝ gA S = gA S ⬝ π) (x y : Fin S.rank → AE D) :
    hermAt S (π *ᵥ x) y = hermAt S x (π *ᵥ y) := by
  have e : (fun i => cA D ((π *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj π := by
    funext i
    rw [adj, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec (cA D) π y i
  have e2 : gA S *ᵥ (π *ᵥ x) = adj π *ᵥ (gA S *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x) h.symm
  rw [hermAt_eq, hermAt_eq, e, e2]
  exact Matrix.dotProduct_mulVec _ _ _

theorem hermAt_smul (S : HSp D) (a : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) y = hermAt S x (cA D a • y) := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermAt_add_left (S : HSp D) (x x' y : Fin S.rank → AE D) :
    hermAt S (x + x') y = hermAt S x y + hermAt S x' y := by
  simp only [hermAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem add_mem_intAt {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem proj_selfAdj {S A L : HSp D} (o : OrthDec S A L) :
    adj (o.jB ⬝ o.pB) ⬝ gA S = gA S ⬝ (o.jB ⬝ o.pB) := by
  rw [o.pB_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_of_half (p : SplitPt D k) {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {π : Mx D S.rank S.rank}
    (h : adj π ⬝ gA S = gA S ⬝ π)
    (hw : ∀ z ∈ latV S M (· = p.v), π *ᵥ (p.e • z) ∈ latV S M (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S M (· = p.v)) : π *ᵥ y ∈ latV S M (· = p.v) := by
  obtain ⟨hs, -, hd⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M p.v hM
  refine (hd _ (mulVec_mem_idAt π (hs y hy))).2 fun x hx => ?_
  have hy' : y = p.e • y + cA D p.e • y := by
    funext i
    rw [← add_smul, Pi.smul_apply, smul_eq_mul]
    exact ((FrameLat.idem_iff p (y i)).1 (hs y hy i)).symm
  rw [hy', Matrix.mulVec_add, hermAt_add_left]
  refine add_mem_intAt ((hd _ (hs _ (hw y hy))).1 (hw y hy) x hx) ?_
  rw [hermAt_mulVec S h, hermAt_smul, GlobalTheory.DualPairCheck.cA_cA, ← Matrix.mulVec_smul]
  exact (hd y (hs y hy)).1 hy _ (hw x hx)

theorem proj_frame {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    (x : n ⊕ Fin 1 → k) :
    (o.jB ⬝ o.pB).map p.pr *ᵥ (α₀.b *ᵥ x) = α₀.b *ᵥ Sum.elim 0 (x ∘ Sum.inr) := by
  have h1 : (o.jB * o.pB).map p.pr * o.jA.map p.pr = 0 := by
    rw [← Matrix.map_mul, Matrix.mul_assoc, o.pB_jA, Matrix.mul_zero]
    exact Matrix.map_zero _ (map_zero _)
  have h2 : (o.jB * o.pB) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      exact RingHom.map_mulVec (incA D) o.iB ζ i
    rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, o.pB_jB, Matrix.mul_one]
  have h3 : (o.jB * o.pB).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = fun i => p.pr (ratV (vecB o ζ) i) := by
    funext i
    have := RingHom.map_mulVec p.pr (o.jB * o.pB) (ratV (vecB o ζ)) i
    rw [h2] at this
    exact this.symm
  rw [IsSumFrame] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_fromCols, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
    ← Matrix.replicateCol_mulVec, h3, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec,
    Matrix.mulVec_zero]

theorem proj_half {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    {M : Lat S} {Λ : Submodule 𝒪[k] (n → k)} (hΛ : α₀.IsLat M (lastKer Λ)) {z : Fin S.rank → AE D}
    (hz : z ∈ latV S M (· = p.v)) : (o.jB ⬝ o.pB) *ᵥ (p.e • z) ∈ latV S M (· = p.v) := by
  have hb : α₀.b *ᵥ (α₀.b' *ᵥ fun i => p.pr (z i)) = fun i => p.pr (z i) := by
    rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
  have h1 : (α₀.b' *ᵥ fun i => p.pr (z i)) ∈ lastKer Λ := by
    refine (hΛ _).2 ?_
    rw [hb]
    simp only [p.sec_pr]
    exact GlobalTheory.FinPlLoc.smul_latV p.v (FrameLat.e_mem_intAt p) hz
  have h2 : (Sum.elim 0 ((α₀.b' *ᵥ fun i => p.pr (z i)) ∘ Sum.inr) : n ⊕ Fin 1 → k) ∈ lastKer Λ :=
    GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨Λ.zero_mem, (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 h1).2⟩
  have h3 := (hΛ _).1 h2
  rw [← proj_frame o ζ h, hb] at h3
  convert h3 using 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← p.sec_pr, RingHom.map_mulVec]
  rfl

theorem lineProj_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ B S α α₀ M LS Λ hM hLS h x hx
  have hπ : ∀ y ∈ latV B.V₀ M P, (B.o.jB * B.o.pB) *ᵥ y ∈ latV B.V₀ M P := by
    intro y hy
    refine (GlobalTheory.FinPlLoc.part_lat P B.V₀ M _ hM.1).2 ⟨mulVec_mem_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
    obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_of_half (p i) hM (proj_selfAdj B.o) (fun z hz => proj_half B.o B.ζ (h i).1 (h i).2 hz)
      (GlobalTheory.FinPlLoc.smul_latV _ he hy)
  obtain ⟨hx1, hx2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P x).1 hx
  have e : (B.o.resS S).symm (0, (B.o.resS S x).2) = x * (B.o.jB * B.o.pB) := by
    rw [OrthDec.resS_symm_apply, OrthDec.resS_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
  rw [e]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx1 i l)
  · have := hx2 _ (hπ y hy)
    rwa [Matrix.mulVec_mulVec] at this

end GlobalTheory.LineProj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DenseRel

variable {D : D7}

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

section Sep

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sepCont_zero : GlobalTheory.Core.Mi.SepCont M 0 := fun τ _ => ⟨0, sobCont_zero _ _, fun _ => by simp⟩

theorem sepCont_add {Λ Λ' : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) (h' : GlobalTheory.Core.Mi.SepCont M Λ') :
    GlobalTheory.Core.Mi.SepCont M (Λ + Λ') := fun τ v => by
  obtain ⟨ℓ, hℓ, e⟩ := h τ v
  obtain ⟨ℓ', hℓ', e'⟩ := h' τ v
  exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by simp [e, e']⟩

theorem sepCont_smul (a : ℂ) {Λ : SmT M →ₗ[ℂ] ℂ} (h : GlobalTheory.Core.Mi.SepCont M Λ) : GlobalTheory.Core.Mi.SepCont M (a • Λ) :=
  fun τ v => by
    obtain ⟨ℓ, hℓ, e⟩ := h τ v
    exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by simp [e]⟩

theorem sepCont_sum {ι : Type} (s : Finset ι) (Λ : ι → SmT M →ₗ[ℂ] ℂ) (h : ∀ i ∈ s, GlobalTheory.Core.Mi.SepCont M (Λ i)) :
    GlobalTheory.Core.Mi.SepCont M (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ (GlobalTheory.Core.Mi.SepCont M) (fun _ _ => sepCont_add M) (sepCont_zero M) h

theorem kill_of_itSpans {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hS : GlobalTheory.Core.Mi.ItSpans M M' It) (Λ : SmT M →ₗ[ℂ] ℂ)
    (h : ∀ P (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y → Λ (It P (PiTensorProduct.tprod ℂ y)) = 0) :
    ∀ v : M.Vec, GlobalTheory.Core.Mi.KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  intro v hv
  have hle : Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧
      x = It P (PiTensorProduct.tprod ℂ y)} ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro x ⟨P, y, hy, rfl⟩
    exact h P y hy
  exact hle (hS v hv)

end Sep

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

end GlobalTheory.SeeSaw.DenseRel


open GlobalTheory.SeeSaw.DenseRel in
theorem GlobalTheory.SeeSaw.perF_rel_of_steps : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (G : ∀ i, (t (s i)).CC j), (∀ s, (t s).Is) → (∀ i a, IsContAut (c.X j) (φ i a)) → ∀ (W W' : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W' S') (It' : PolF D W'.rank (c.V (j + 1)).rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT (c.M (j + 1))), GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) M' It' → (∀ P₁ P₂ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 (c.It j P₁ (It' P₂ v))) = 0) → ∀ v, ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 v) = 0 := by
  intro hHC D c 𝒯 t hc j ρ h I _ s α φ G ht hφ _W W' S' M' It' hS' hrel
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega

  have hmult : ∀ i, ∃ J χ, (G i).1 ∈ MultT c.θ (c.M j) J χ := fun i => by
    obtain ⟨J, χ, hle⟩ := (ht (s i)).CC j hj
    exact ⟨J, χ, hle (G i).2⟩
  choose J χ hG using hmult
  have hcont : ∀ i x, IsContAut (c.V j) ((G i).1 x) := fun i x => isContAut_multT (hG i) x

  have hL : ∀ (i : I) (a : (t (s i)).Ch j) (g : GA D (c.V j)), ∃ Λ : SmT (c.M j) →ₗ[ℂ] ℂ, GlobalTheory.Core.Mi.SepCont (c.M j) Λ ∧
      ∀ x, Λ x = (c.B j ρ h).per c.ψ (φ i a) (rTrans g ((G i).1 x)) := fun i a g =>
    GlobalTheory.T.besselPeriod_rightTranslate_sobolevSepContinuous D c.θ c.ψ ρ (c.B j ρ h) (c.par j) (c.M j) (J i) (χ i) g (φ i a) hc.inf hc.std (hφ i a) (G i).1 (hG i)
  choose L hLs hLe using hL
  let Λ : SmT (c.M j) →ₗ[ℂ] ℂ :=
    ∑ i, α i • ∑ a, ∑ g ∈ ((t (s i)).e j a).support, ((t (s i)).e j a g) • L i a g
  have hΛ : ∀ x, Λ x = ∑ i, α i * (t (s i)).perF j ρ h (φ i) ((G i).1 x) := by
    intro x
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hLe]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold Tup.perF
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B j ρ h) (φ i a) (hφ i a)).2 _ _ (hcont i x)).2]
  have hΛs : GlobalTheory.Core.Mi.SepCont (c.M j) Λ :=
    sepCont_sum _ _ _ fun i _ => sepCont_smul _ _ (sepCont_sum _ _ _ fun a _ =>
      sepCont_sum _ _ _ fun g _ => sepCont_smul _ _ (hLs i a g))
  have hK : ∀ v : (c.M j).Vec, GlobalTheory.Core.Mi.KVecP (c.M j) v → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
    refine kill_of_itSpans (c.M j) (c.M (j + 1)) (c.It j) (hc.span j hj1) Λ fun P y hy => ?_
    exact kill_of_itSpans (c.M (j + 1)) M' It' hS' (Λ ∘ₗ c.It j P)
      (fun P₂ z _ => by simp only [LinearMap.comp_apply, hΛ]; exact hrel P P₂ _) y hy
  have h0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D (c.V j) (c.par j) (c.M j) Λ hΛs hK
  intro v
  rw [← hΛ v, h0, LinearMap.zero_apply]

end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens


theorem _root_.GlobalTheory.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ _root_.GlobalTheory.Size.thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  first | exact @GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | exact GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | (intros; apply GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDiag

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

theorem coord_zmod (I : AutInst) (g : ℕ) {β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : IsFrame β I.L) {v : VA I}
    (hv : v ∈ mL I g) (i : Fin I.n) :
    ZMod' I g ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v) i) := by
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.RowIndex.mem_mL.1 hv
  have hz' : z ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by rw [hatL_eq]; exact hz
  refine ⟨_, (hβ z).1 hz' i, ?_⟩
  rw [Matrix.mulVec_smul]
  rfl

theorem diag_mod_in_frame : ∀ (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (Y : I.Gf) (d : Fin I.n → Formalism.L2.Herm.intAf I.F I.E), IsLiftFrame I g b β → (∀ y ∈ I.Lf, I.fmat Y *ᵥ y ∈ I.Lf) → (∀ y ∈ I.Lf, I.fmat Y⁻¹ *ᵥ y ∈ I.Lf) → (∀ j : Fin I.n, I.fmat Y *ᵥ b j.val - (d j).1 • b j.val ∈ mL I g) → ∃ x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), frGL β x = (Y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∧ ∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - Matrix.diagonal d) i j).1 := by
  intro I g b β Y d hβ hY hYi hd
  have hK : Y ∈ I.Kset := by
    intro y
    refine ⟨fun hy => hY y hy, fun hy => ?_⟩
    have h := hYi _ hy
    have e : I.fmat Y⁻¹ * I.fmat Y = 1 := by
      show (((Y⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * _ = 1
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  obtain ⟨x, hx⟩ := (kset_iff I hβ.1 Y).1 hK
  refine ⟨x, hx, fun i j => ?_⟩
  have hconj : β⁻¹ * frGL β x * β = intGL I.F I.E I.n x := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hx] at hconj
  set col : VA I := fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j with hcol
  have hw : I.fmat Y *ᵥ col - (d j).1 • col ∈ mL I g := by
    have h1 := hβ.2 j
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.RowIndex.mem_mL.1 h1
    have h2 : I.fmat Y *ᵥ (col - b j.val) ∈ mL I g := by
      rw [show col - b j.val = _ from hz']
      exact Formalism.L2.SG.Pf.unitaryCongruence.mL_mv I hY g le_rfl z hz
    have h3 : (d j).1 • (col - b j.val) ∈ mL I g := (mL I g).smul_mem (d j) h1
    have e : I.fmat Y *ᵥ col - (d j).1 • col =
        (I.fmat Y *ᵥ b j.val - (d j).1 • b j.val) + I.fmat Y *ᵥ (col - b j.val) - (d j).1 • (col - b j.val) := by
      rw [Matrix.mulVec_sub, smul_sub]
      abel
    rw [e]
    exact sub_mem (add_mem (hd j) h2) h3
  have key := coord_zmod I g hβ.1 hw i
  convert key using 1
  have eA : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ (I.fmat Y *ᵥ col)) i =
      ((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).1 := by
    rw [Matrix.mulVec_mulVec]
    show ((((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) * I.fmat Y) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    rfl
  have eB : (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ col) i =
      if i = j then 1 else 0 := by
    show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))) i j = _
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, eA, eB, Matrix.sub_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp
  · simp

end GlobalTheory.FrameDiag

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

theorem orth_and_eq_eSum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (J : List ι) (P : Pl D → Prop), Places p J P → ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset → (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) → (∀ i j, i ≠ j → (p i).e * (p j).e = 0) ∧ e = GlobalTheory.FinPl.PutIn.eSum p J := by
  intro D k _ _ _ _ ι p J P hP Pset e he hq
  classical
  obtain ⟨q, hq⟩ := hq
  refine ⟨fun i j hij => ?_, ?_⟩
  · refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (p i).split (p j).split).resolve_left fun h => hij ?_
    exact q.injective (Subtype.ext (GlobalTheory.PlaceVec.isIdemAt_inj (hq i) (h ▸ hq j)))
  · obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    haveI : Fintype ι := Fintype.ofList J hP.all
    have h1 : ∀ i, es (q i).1 = (p i).e := fun i =>
      GlobalTheory.SplitHeckeAdj.idem_unique D.sp.X' (hq i) (hes _ (q i).2)
    have h2 : J.toFinset = Finset.univ := Finset.eq_univ_of_forall fun i => List.mem_toFinset.2 (hP.all i)
    rw [eSum, ← List.sum_toFinset _ hP.nodup, h2, ← Finset.sum_coe_sort Pset es, ← Equiv.sum_comp q]
    exact Finset.sum_congr rfl fun i _ => h1 i

end GlobalTheory.FinPl.PutIn

end
end
