module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle440
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MonoIdele

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def diagU (b : Fin ρ → (AE D)ˣ) : GL (Fin ρ) (AE D) :=
  ⟨Matrix.diagonal fun i => (b i : AE D), Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem diagU_inv_val (b : Fin ρ → (AE D)ˣ) :
    ((diagU b)⁻¹).1 = Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D) := rfl

theorem diagU_inv_inv_val (b : Fin ρ → (AE D)ˣ) :
    (((diagU b)⁻¹)⁻¹).1 = Matrix.diagonal fun i => (b i : AE D) := by rw [inv_inv]; rfl

theorem mulVec_supp {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {P : Pl D → Prop} {z : Fin n → AE D}
    (hz : ∀ j, z j ∈ idAt D P) (k : Fin m) : (A *ᵥ z) k ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hz j)

theorem mt_mulVec_inv (g : GA D S) (z : Fin S.rank → AE D) : mt S g *ᵥ (mt S g⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel]
  exact Matrix.one_mulVec z

theorem mem_iff_of_moves {L M : Lat S} {v : Pl D} {g : GA D S} (hm : Moves S g L M (· = v)) (z : Fin S.rank → AE D) :
    z ∈ latV S M (· = v) ↔ mt S g⁻¹ *ᵥ z ∈ latV S L (· = v) := by
  constructor
  · intro hz
    have hs : ∀ k, z k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    rw [hm _ (fun k => mulVec_supp _ hs k), mt_mulVec_inv]
    exact hz
  · intro hz
    have hs : ∀ k, (mt S g⁻¹ *ᵥ z) k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    have h := (hm _ hs).1 hz
    rwa [mt_mulVec_inv] at h

theorem diagonal_mulVec_single {n : ℕ} (u : Fin n → AE D) (i : Fin n) (c : AE D) :
    Matrix.diagonal u *ᵥ Pi.single i c = Pi.single i (u i * c) := by
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem adj_diagonal {n : ℕ} (u : Fin n → AE D) :
    adj (Matrix.diagonal u) = Matrix.diagonal fun i => cA D (u i) := by
  ext i j
  show cA D (Matrix.diagonal u j i) = Matrix.diagonal (fun k => cA D (u k)) i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, map_zero]

variable (d : HypDec S S₀ ρ)

theorem levi_colMul_jX (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jX i c = colMul d.jX i (u i * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jX, ← Matrix.mulVec_mulVec, ha,
    diagonal_mulVec_single]

theorem levi_colMul_jY (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jY i c = colMul d.jY i (cA D (u i) * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jY, ← Matrix.mulVec_mulVec, ha,
    adj_diagonal, diagonal_mulVec_single]

theorem pX_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (y : Fin S.rank → AE D)
    (i : Fin ρ) : (d.pX *ᵥ (mt S (d.levi a) *ᵥ y)) i = u i * (d.pX *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_diagonal]

theorem pY_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u)
    (y : Fin S.rank → AE D) (i : Fin ρ) : (d.pY *ᵥ (mt S (d.levi a) *ᵥ y)) i = cA D (u i) * (d.pY *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec, ha, adj_diagonal, Matrix.mulVec_diagonal]

theorem wittProjAnisotropic_mulVec_levi_eq (a : GL (Fin ρ) (AE D)) (y : Fin S.rank → AE D) :
    d.p0 *ᵥ (mt S (d.levi a) *ᵥ y) = d.p0 *ᵥ y := by
  rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem mem_dualC_one (c : D.host.E) : c ∈ SplitLat.dualC (1 : FI D) ↔ c ∈ (1 : FI D) := by
  rw [SplitLat.mem_dualC, FractionalIdeal.mem_one_iff]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    exact ⟨o, by rw [ho, star_one, one_mul]⟩
  · rintro ⟨o, rfl⟩ b hb
    obtain ⟨o', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨r, hr⟩ := GlobalTheory.HypLattice.star_mem_int ⟨o', rfl⟩
    exact ⟨r * o, by rw [map_mul, hr]⟩

variable (L₀ : Lat S₀)

theorem line_splitL_jY (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jY i a ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v) ↔ a ∈ idV (1 : FI D) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v), (d.pY *ᵥ y) i ∈ idV (1 : FI D) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qY *ᵥ _) i ∈ _
        rw [SplitLat.rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact (mem_dualC_one _).1 (((SplitLat.mem_splitL d L₀ _ x).1 hx).2.2 i)
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.pY_jY, Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jY i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e' *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [SplitLat.colMul_eq_mulVec]
        change rat d.e' *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, SplitLat.rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        SplitLat.e'_mem (SplitLat.single_mem_of_mem (I := fun _ => SplitLat.dualC (1 : FI D)) i ((mem_dualC_one _).2 hb)), rfl⟩
    | zero =>
      have : colMul d.jY i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jY i (z + z') = colMul d.jY i z + colMul d.jY i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jY i (-z) = -colMul d.jY i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.FinPl.MonoIdele


open GlobalTheory.FinPl.MonoIdele in
theorem GlobalTheory.FinPl.exists_selfDual_mono_idele : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ : Lat S₀), IsSelfDualC S₀ L₀ → ∀ b : Fin ρ → (AE D)ˣ, ∃ L : Lat S, IsSelfDualC S L ∧ ∀ x : Pl D, MonoAt d L L₀ x ∧ (∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x) := by
  intro D S S₀ ρ d L₀ hL₀ b
  have hL1 : IsSelfDualC S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) :=
    SplitLat.isSelfDualC_splitL d (fun _ => one_ne_zero) hL₀
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S _ hL1).1 (d.levi (diagU b))
  refine ⟨M, hM, fun x => ⟨?_, fun i a _ => ?_, fun i a _ => ?_⟩⟩
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    intro y
    rw [key y, SplitLat.monoAt_splitL d L₀ (fun _ => (1 : FI D)) x (mt S (d.levi (diagU b)⁻¹) *ᵥ y)]
    simp only [key, levi_colMul_jX d _ (diagU_inv_val b), levi_colMul_jY d _ (diagU_inv_inv_val b),
      pX_levi_mulVec d _ (diagU_inv_val b), pY_levi_mulVec d _ (diagU_inv_inv_val b), wittProjAnisotropic_mulVec_levi_eq]
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jX d _ (diagU_inv_val b)]
    exact (SplitLat.line_splitL d L₀ _ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jY d _ (diagU_inv_inv_val b)]
    exact (line_splitL_jY d L₀ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.mem_twistPlaceLevel_single_place_character : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.LevGlue.mem_levS_datY_single | exact GlobalTheory.LevGlue.mem_levS_datY_single | (intros; apply GlobalTheory.LevGlue.mem_levS_datY_single <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

theorem _root_.GlobalTheory.T.transvectionStable_localLattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  first | exact @GlobalTheory.LatPairStab.stable_lattice_shape | exact GlobalTheory.LatPairStab.stable_lattice_shape | (intros; apply GlobalTheory.LatPairStab.stable_lattice_shape <;> assumption)
end
