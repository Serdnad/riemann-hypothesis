module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle045
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.exists_selfDual_lattice_patched_at_places : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D), ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧ ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  first | exact @GlobalTheory.FinPl.Patch.patch | exact GlobalTheory.FinPl.Patch.patch | (intros; apply GlobalTheory.FinPl.Patch.patch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MidVacLat

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv_mulVec (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul', mul_inv_cancel, mt_one', Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) : GlobalTheory.FinPl.Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv_mulVec] at e
  exact e.symm

theorem smul_mem_latA {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ GlobalTheory.FinPl.latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ GlobalTheory.FinPl.latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latA S L P) :
    mt S g *ᵥ z ∈ GlobalTheory.FinPl.latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ GlobalTheory.FinPl.latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_mem_latO {S T : HSp D} {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S}
    {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · show (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) i j ∈ _
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ GlobalTheory.FinPl.latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_smul_left {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    actO S T g h (e • x) = e • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_two_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  simp only [two_nsmul, actO, Matrix.mul_add, Matrix.add_mul]

theorem isHalf_actO {S T : HSp D} (g : GA D S) (h : GA D T) {e : AE D} {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • x = x := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hx i j
  intro i j
  have := congrFun (congrFun (actO_smul_left g h e x) i) j
  rw [hx'] at this
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  show HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹⁻¹))) (mt S g⁻¹) = x
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, ← mt_mul' S g g⁻¹, mul_inv_cancel,
    mt_one', Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul' T h h⁻¹, mul_inv_cancel,
    mt_one', Matrix.one_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T}
    (hb : GlobalTheory.FinPl.Moves S b Λ M fun _ => True) (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' fun _ => True) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f) := by
  have key : ∀ u, u ∈ latO S T (M : Set _) (M' : Set _) (fun _ => True) → actO S T b⁻¹ b'⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) fun _ => True :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb') hu
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hw := key u hu
    have h2 : 2 • u = actO S T b b' (2 • actO S T b⁻¹ b'⁻¹ u) := by
      rw [actO_two_nsmul, actO_actO_inv]
    rw [h2, ← hW.om_heis b b' _ f hf, hv.1 _ hw]
  · have hw := key u hu
    have h1 : u = actO S T b b' (actO S T b⁻¹ b'⁻¹ u) := (actO_actO_inv b b' u).symm
    rw [h1, ← hW.om_heis b b' _ f hf, hv.2 e he _ hw (isHalf_actO _ _ hh)]

end GlobalTheory.MidVacLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.FrameLat

theorem moves_iff_smul_eq : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n) (L : GlobalTheory.FinPl.Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → β.IsLat L Λ → ∀ (κ : GA D S) (g : GL n k), (mt S κ).map p.pr = β.b * g.val * β.b' → (GlobalTheory.FinPl.Moves S κ L L (· = p.v) ↔ g • Λ = Λ) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ κ g hg
  have hsec : ∀ u : Fin S.rank → k, mt S κ *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i) := by
    intro u
    funext i
    rw [← hg]

    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have key : ∀ x : n → k, mt S κ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) =
      fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i) := by
    intro x
    rw [hsec, Matrix.mulVec_mulVec, Matrix.mul_assoc, β.b'b, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  constructor
  · intro hm
    have hiff : ∀ x, x ∈ Λ ↔ g • x ∈ Λ := by
      intro x
      rw [hΛ, hΛ]
      change _ ∈ latV S L _ ↔ (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i)) ∈ latV S L _
      rw [hm _ (fun i => sec_mem_idAt p _), key]
    ext x
    rw [GlobalTheory.LatPair.mem_smul_iff, hiff, smul_inv_smul]
  · intro hgΛ
    have hinv : ∀ x, g • x ∈ Λ ↔ x ∈ Λ := by
      intro x
      conv_lhs => rw [← hgΛ]
      rw [GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul]
    have hE : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) ↔
        (fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i)) ∈ latV S L (· = p.v) := by
      intro u
      have hu : u = β.b *ᵥ (β.b' *ᵥ u) := by rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      have hAu : (β.b * g.val * β.b') *ᵥ u = β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have h := hinv (β.b' *ᵥ u)
      rw [hΛ, hΛ] at h
      change (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u))) i)) ∈ latV S L _ ↔
        (fun i => p.sec ((β.b *ᵥ (β.b' *ᵥ u)) i)) ∈ latV S L _ at h
      rw [← hu, ← hAu] at h
      exact h.symm
    have hAA : ∀ x : Fin S.rank → k, (β.b * g.val * β.b') *ᵥ ((β.b * (g⁻¹).val * β.b') *ᵥ x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul, ← Matrix.mul_assoc g.val, Units.mul_inv,
        Matrix.one_mul, β.bb', Matrix.one_mulVec]
    have hunit : ∀ x z : Fin S.rank → k,
        ∑ i, ∑ j, ((β.b * g.val * β.b') *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
          (((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      intro x z
      have h := pairing_inv (p := p) κ x z
      rwa [hg] at h
    have hC : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔
        (fun i => cA D (p.sec ((((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) i))) ∈ latV S L (· = p.v) := by
      intro z
      rw [csec_mem_iff hL, csec_mem_iff hL]
      constructor
      · intro h x hx
        have hx' : (fun i => p.sec (((β.b * (g⁻¹).val * β.b') *ᵥ x) i)) ∈ latV S L (· = p.v) := by
          rw [hE, hAA]; exact hx
        have h2 := hunit ((β.b * (g⁻¹).val * β.b') *ᵥ x) z
        rw [hAA] at h2
        rw [h2]; exact h _ hx'
      · intro h x hx
        rw [← hunit x z]; exact h _ ((hE x).1 hx)
    intro y hy
    have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
      funext i
      simp only [Pi.add_apply, p.sec_pr]
      rw [map_mul, cA_cA, ← add_mul]
      exact ((idem_iff p _).1 (hy i)).symm
    obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
      ⟨_, _, hyd⟩
    rw [Matrix.mulVec_add, hsec u, mt_csec κ z, decomp hL, decomp hL, hE u, hC z]

end GlobalTheory.FinPl.FrameLat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitPrimJac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colPair (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ r, ∑ t, q.pr (incA D (x r)) * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (y t))) =
      q.pr (incA D (star (∑ r, ∑ t, star (x r) * HSpace.gram S r t * y t))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.FinPl.FrameLat.cA_incA, star_sum, star_mul', star_star, map_sum, map_mul]

theorem mat_entry (S : HSp D) {m n : Type} [Fintype m] [Fintype n] (A : Matrix (Fin S.rank) m D.host.E)
    (B : Matrix (Fin S.rank) n D.host.E) (b : m) (i : n) :
    (Aᴴ * HSpace.gram S * B) b i = ∑ r, ∑ t, star (A r b) * HSpace.gram S r t * B t i := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem colPair_smul (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (c : k) (x y : Fin S.rank → D.host.E)
    (col : Fin S.rank → k) (hcol : ∀ r, col r = c * q.pr (incA D (x r))) :
    ∑ r, ∑ t, col r * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (y t))) =
      c * q.pr (incA D (star (∑ r, ∑ t, star (x r) * HSpace.gram S r t * y t))) := by
  rw [← colPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hcol]; ring

end GlobalTheory.SplitPrimJac
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitInt

theorem intAt_iff_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  have he := GlobalTheory.UpMem.finPart_e_int q
  rw [q.int_iff, q.int_iff, q.sec_pr, q.sec_pr, map_mul, map_mul]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h,
      GlobalTheory.FinPl.FrameLat.mul_mem_intAE he (GlobalTheory.IdemSupport.finPart_cA_mem h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    have hsum : a = q.e * a + cA D (q.e * cA D a) := by
      rw [map_mul, Formalism.L2.Theta.cA_cA, ← add_mul]
      exact ((GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha).symm
    have h3 : finPart D (cA D (q.e * cA D a)) ∈ intAE D := by
      apply GlobalTheory.IdemSupport.finPart_cA_mem
      rw [map_mul]; exact h2
    rw [hsum, (finPart D).map_add, (finPart D).map_mul]
    exact add_mem h1 h3

end GlobalTheory.SplitInt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem supp_mulVec' {D : D7} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {I : Ideal (AE D)} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (X *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem colMul_zero' {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext r; simp [colMul]

theorem glued_stab_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (g : GL n k) :
    GlobalTheory.RootEx.embX 1 g • gluedS q 1 P.ker P.vec = gluedS q 1 P.ker P.vec ↔ g • P = P := by
  rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, Pair.smul_eq_iff P.hasVal_vec]
  constructor
  · intro h
    have h1 : g • P.ker = P.ker := by
      have := GlobalTheory.LevelUnfold.interX_gluedS (q := q) (le_refl 1) (g • P.ker) (g • P.vec)
      rw [h, GlobalTheory.LevelUnfold.interX_gluedS (le_refl 1)] at this
      exact this.symm
    refine ⟨h1, ?_⟩
    have h2 := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) (g • P.ker) (g • P.vec)
    rw [h] at h2
    exact (GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (le_refl 1)).1 h2
  · rintro ⟨h1, h2⟩
    rw [h1]
    exact GlobalTheory.LevelUnfold.gluedS_congr h2

theorem moves_emb_iff {D : D7} {S A B : HSp D} (o : OrthDec S A B) (M : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A)
    (LB : GlobalTheory.FinPl.Lat B) (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.OrthAt o M LA LB v) (κ : GA D A) :
    GlobalTheory.FinPl.Moves S (o.emb (κ, 1)) M M (· = v) ↔ GlobalTheory.FinPl.Moves A κ LA LA (· = v) := by
  have e1 : ∀ y, o.pA *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = Formalism.L2.Theta.mt A κ *ᵥ (o.pA *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact o.pA_emb κ 1
  have e2 : ∀ y, o.pB *ᵥ (Formalism.L2.Theta.mt S (o.emb (κ, 1)) *ᵥ y) = o.pB *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, o.pB_emb]; simp [Formalism.L2.Theta.mt]
  constructor
  · intro hM yA hyA
    have hy : ∀ i, (o.jA *ᵥ yA) i ∈ idAt D (· = v) := supp_mulVec' _ hyA
    have hA1 : o.pA *ᵥ (o.jA *ᵥ yA) = yA := by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
    have hB1 : o.pB *ᵥ (o.jA *ᵥ yA) = 0 := by rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]
    have := hM _ hy
    rw [h, h, e1, e2, hA1, hB1] at this
    simpa only [zero_mem, and_true] using this
  · intro hA y hy
    rw [h, h, e1, e2, ← hA _ (supp_mulVec' _ hy)]

theorem carriesLattice_wittEmbedding_iff_core {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N : GlobalTheory.FinPl.Lat S) (M : GlobalTheory.FinPl.Lat S₀)
    (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.MonoAt d N M v) (g : GA D S₀) :
    GlobalTheory.FinPl.Moves S (d.emb0 g) N N (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g M M (· = v) := by
  have eX : ∀ y, d.pX *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have eY : ∀ y, d.pY *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have e0 : ∀ y, d.p0 *ᵥ (Formalism.L2.Theta.mt S (d.emb0 g) *ᵥ y) = Formalism.L2.Theta.mt S₀ g *ᵥ (d.p0 *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact d.wittDecomp_projAnisotropic_anisotropicEmbedding g
  constructor
  · intro hM y₀ hy₀
    have hy : ∀ i, (d.j0 *ᵥ y₀) i ∈ idAt D (· = v) := supp_mulVec' _ hy₀
    have hX1 : d.pX *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
    have hY1 : d.pY *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
    have h01 : d.p0 *ᵥ (d.j0 *ᵥ y₀) = y₀ := by rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
    have := hM _ hy
    rw [h, h, eX, eY, e0, hX1, hY1, h01] at this
    simpa only [Pi.zero_apply, colMul_zero', zero_mem, true_and, implies_true] using this
  · intro hA y hy
    rw [h, h, eX, eY, e0, ← hA _ (supp_mulVec' _ hy)]

theorem exists_gl_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n)
    (κ : GA D S) : ∃ g : GL n k, (mt S κ).map p.pr = β.b * g.val * β.b' := by
  have e1 : mt S κ * mt S κ⁻¹ = 1 := by
    rw [show mt S κ * mt S κ⁻¹ = mt S (κ * κ⁻¹) from rfl, mul_inv_cancel]; rfl
  have e2 : mt S κ⁻¹ * mt S κ = 1 := by
    rw [show mt S κ⁻¹ * mt S κ = mt S (κ⁻¹ * κ) from rfl, inv_mul_cancel]; rfl
  have hM : (mt S κ).map p.pr * (mt S κ⁻¹).map p.pr = 1 := by
    rw [← Matrix.map_mul, e1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM' : (mt S κ⁻¹).map p.pr * (mt S κ).map p.pr = 1 := by
    rw [← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨β.b' * (mt S κ).map p.pr * β.b, β.b' * (mt S κ⁻¹).map p.pr * β.b, ?_, ?_⟩, ?_⟩
  · calc β.b' * (mt S κ).map p.pr * β.b * (β.b' * (mt S κ⁻¹).map p.pr * β.b)
          = β.b' * ((mt S κ).map p.pr * (β.b * β.b') * (mt S κ⁻¹).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM, Matrix.mul_one, β.b'b]
  · calc β.b' * (mt S κ⁻¹).map p.pr * β.b * (β.b' * (mt S κ).map p.pr * β.b)
          = β.b' * ((mt S κ⁻¹).map p.pr * (β.b * β.b') * (mt S κ).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM', Matrix.mul_one, β.b'b]
  · show _ = β.b * (β.b' * (mt S κ).map p.pr * β.b) * β.b'
    calc (mt S κ).map p.pr = (β.b * β.b') * (mt S κ).map p.pr * (β.b * β.b') := by
          rw [β.bb', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.OffTrace

end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  first | exact @GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | exact GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | (intros; apply GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff <;> assumption)
end
