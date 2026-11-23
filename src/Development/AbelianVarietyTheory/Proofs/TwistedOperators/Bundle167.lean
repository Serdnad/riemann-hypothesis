module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle158
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heisO_add_fun (S T : HSp D) (u : WO S T) (G H : WO S T → ℂ) :
    heisO ψ S T u (G + H) = heisO ψ S T u G + heisO ψ S T u H := by
  funext w
  simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_smul_fun (S T : HSp D) (u : WO S T) (c : ℂ) (G : WO S T → ℂ) :
    heisO ψ S T u (c • G) = c • heisO ψ S T u G := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem integrableOn_heisO (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (u a : WO V W) :
    IntegrableOn (fun z => heisO ψ V W u G (isoPart V W C z + a)) 𝓨 μ := by
  obtain ⟨-, -, hvol⟩ := h
  obtain ⟨c, hc⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hcont : Continuous (fun z => heisO ψ V W u G (isoPart V W C z + a)) :=
    (GlobalTheory.HeisOrtho.continuous_heisO hψ.1 hG.cont u).comp ((continuous_isoPart V W C).add continuous_const)
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound hcont.aestronglyMeasurable c (Filter.Eventually.of_forall fun z => ?_)
  rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  exact hc _

theorem term_linear : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h y
  have key : ∀ G, IsThetaFunO ψ V W G → IntegrableOn
      (fun z => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G (isoPart V W C z + midPart V V' W B 0)) 𝓨 μ :=
    fun G hG => integrableOn_heisO V W C hψ h hG _ _
  refine ⟨fun G H hG hH => ?_, fun c G hG => ?_⟩
  · simp only [term, res, heisO_add_fun, Pi.add_apply]
    exact integral_add (key G hG) (key H hH)
  · simp only [term, res, heisO_smul_fun, Pi.smul_apply, smul_eq_mul]
    first
      | exact integral_const_mul c _
      | exact integral_mul_left c _

end GlobalTheory.MixedTerm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelDatumValue_eq_prod_localResidueValues : ∀ (D : D7) (a b : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Hl : ∀ PP : ↥L.Pg, Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP.1))) (cl : ∀ PP : ↥L.Pg, Hl PP →* ℂˣ),
    L.P = Formalism.L2.DIV.LevelP.ofLocal Hl cl →
    ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χ y = ∏ PP : ↥L.Pg, gLoc L PP.1 (Hl PP) (cl PP) (χ PP.1) (y PP.1) := by
  first | exact @GlobalTheory.StepVec.omegaG_eq_prod_gLoc | exact GlobalTheory.StepVec.omegaG_eq_prod_gLoc | (intros; apply GlobalTheory.StepVec.omegaG_eq_prod_gLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b t : ℕ) (ht : a + t = b) (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ)
    (J : Subgroup (GL (Fin a) (v.adicCompletionIntegers D.host.F))) (lam : J →* ℂˣ), IsLocLevel φ PP L H c J lam →
    ∀ (mu : (Fv D.host.F v)ˣ →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu χ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v),
      localNewformFunction v J lam mu (rowsTB ht Y) = viaRed r (gLoc (b := b) L PP H c χ) Y := by
  first | exact @GlobalTheory.StepVec.locDatum_eq_viaRed | exact GlobalTheory.StepVec.locDatum_eq_viaRed | (intros; apply GlobalTheory.StepVec.locDatum_eq_viaRed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaTwistDatum_eq_function_of_residueReduction : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsRedMap φ PP r →
    ∀ (a b k : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), LiftsChar φ PP mu ξ⁻¹ →
    ∀ Y : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v k mu Y = viaRed r (qLoc k PP ξ) Y := by
  first | exact @GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | exact GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc | (intros; apply GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRange

theorem range_sum_eq_eig {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) (χ : P → ℂ) (E : G → ℂ) (k : ℂ) (hk : k ≠ 0) (h0 : ∀ g, g ∉ P → E g = 0)
    (h1 : ∀ g : P, E g * χ g = k) (hm : ∀ a b : P, χ (a * b) = χ a * χ b) :
    LinearMap.range (∑ g, E g • ρ g) = eig ρ P χ := by
  classical
  have hs : ∀ (p : P) (g : G), E g = χ p * E (p * g) := by
    intro p g
    by_cases hg : g ∈ P
    · have e1 := h1 ⟨g, hg⟩
      have e2 := h1 (p * ⟨g, hg⟩)
      rw [hm] at e2
      have hne : χ ⟨g, hg⟩ ≠ 0 := by
        intro h; rw [h, mul_zero] at e1; exact hk e1.symm
      apply mul_right_cancel₀ hne
      simp only [Subgroup.coe_mul] at e1 e2
      rw [e1, ← e2]; ring
    · have : (p : G) * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      rw [h0 g hg, h0 _ this, mul_zero]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_eig]
    intro p

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft (p : G)) (fun g => χ p • E g • ρ g y)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hs p g, Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, mul_smul]
  · intro x hx
    rw [mem_eig] at hx
    have hT : (∑ g, E g • ρ g) x = (∑ g : G, if g ∈ P then k else 0) • x := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ P
      · rw [if_pos hg, ← h1 ⟨g, hg⟩, mul_smul, ← hx ⟨g, hg⟩]
      · rw [if_neg hg, h0 g hg, zero_smul, zero_smul]
    have hne : (∑ g : G, if g ∈ P then k else 0) ≠ 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_ne_zero ?_ hk
      have : (Finset.univ.filter fun g : G => g ∈ P).Nonempty := ⟨1, by simp⟩
      exact_mod_cast this.card_pos.ne'
    refine ⟨(∑ g : G, if g ∈ P then k else 0)⁻¹ • x, ?_⟩
    rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem range_mul_eq_inf {M : Type} [AddCommGroup M] [Module ℂ M] (C T : Module.End ℂ M) (hC : C * C = C)
    (hc : C * T = T * C) : LinearMap.range (C * T) = LinearMap.range T ⊓ LinearMap.ker (C - LinearMap.id) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨C y, ?_⟩, ?_⟩
    · rw [hc]; rfl
    · have : C (C (T y)) = C (T y) := by rw [← Module.End.mul_apply, hC]
      simp [this]
  · rintro _ ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using h

theorem op_comp {G H M : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup M] [Module ℂ M]
    (Φ : G ≃* H) (ρ : Representation ℂ G M) (e : H → ℂ) :
    GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) e = ∑ g, e (Φ g) • ρ g := by
  unfold GlobalTheory.BadShare.op
  rw [← Equiv.sum_comp Φ.toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp

theorem tens_e_mul {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ * ∏ v, (L v).chi (γ v) = ∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹ := by
  unfold GlobalTheory.BadShare.tens
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := GlobalTheory.BadShare.Basic.chi_ne (L v) (γ v)
  simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_pos (h v)]
  field_simp

theorem tens_e_zero {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ¬ ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ = 0 := by
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_neg hv])

theorem prod_card_ne {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N) :
    (∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_
  haveI : Nonempty {u // (L v).Mem u} := ⟨⟨1, GlobalTheory.BadShare.Basic.mem_one (L v)⟩⟩
  exact_mod_cast Nat.card_pos.ne'

theorem ranges : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  intro g₁ g₂ N _ _ ι₁ ι₂ G M _ _ _ _ _ _ _ _ Φ L₁ L₂ P χ ρ _ c hP hχ hcc hc
  have key : LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ := by
    rw [op_comp]
    refine range_sum_eq_eig ρ P χ _ _ (mul_ne_zero (prod_card_ne L₁) (prod_card_ne L₂)) ?_ ?_ ?_
    · intro g hg
      rw [hP, not_and_or] at hg
      unfold GlobalTheory.BadShare.tens2
      rcases hg with h | h
      · rw [tens_e_zero _ _ h, zero_mul]
      · rw [tens_e_zero L₂ _ h, mul_zero]
    · intro g
      obtain ⟨h1, h2⟩ := (hP g).1 g.2
      rw [hχ, ← tens_e_mul L₁ _ h1, ← tens_e_mul L₂ _ h2]
      unfold GlobalTheory.BadShare.tens2
      ring
    · intro a b
      obtain ⟨a1, a2⟩ := (hP a).1 a.2
      obtain ⟨b1, b2⟩ := (hP b).1 b.2
      rw [hχ, hχ, hχ]
      simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
      simp only [fun v => GlobalTheory.BadShare.Basic.chi_mul (L₁ v) (a1 v) (b1 v),
        fun v => GlobalTheory.BadShare.Basic.chi_mul (L₂ v) (a2 v) (b2 v), Finset.prod_mul_distrib]
      ring
  refine ⟨key, ?_⟩
  rw [GlobalTheory.BadShare.Basic.op_conv, range_mul_eq_inf, key, op_comp]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hcc]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hc, GlobalTheory.BadShare.Basic.op_conv]

end GlobalTheory.LevRange
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodProjProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem monicOf_injective {g N : ℕ} [Fact g.Prime] :
    Function.Injective fun c : Fin N → ZMod g => (Formalism.CyclotomicNorms.monicOf c : (ZMod g)[X]) := by
  intro c c' h
  funext i
  have key := congrArg (fun p : (ZMod g)[X] => p.coeff (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt i.isLt, if_false, zero_add] at key
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl,
    Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl] at key


open Classical in
theorem sum_good {g N m : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] [Fintype (ι → Fin N → ZMod g)]
    (ch : ι → Fin m → (ZMod g)ˣ) (h : (ι → (ZMod g)[X]) → ℂ) :
    (∑ a : ι → Fin N → ZMod g, if GlobalTheory.BadShare.Good g N ch (fun v => Formalism.CyclotomicNorms.monicOf (a v)) then
      h (fun v => Formalism.CyclotomicNorms.monicOf (a v)) else 0) = ∑ F ∈ GlobalTheory.BadShare.goodSet g N ch, h F := by
  have hinj : Function.Injective fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) :=
    by
      intro a b hab
      funext v
      have hv : Formalism.CyclotomicNorms.monicOf (a v) = (Formalism.CyclotomicNorms.monicOf (b v) : (ZMod g)[X]) := congrFun hab v
      exact monicOf_injective (g := g) (N := N) hv
  have hset : GlobalTheory.BadShare.goodSet g N ch =
      (Finset.univ.filter fun a : ι → Fin N → ZMod g => GlobalTheory.BadShare.Good g N ch fun v => Formalism.CyclotomicNorms.monicOf (a v)).image
        fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) := by
    ext F
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hF
      have hG := GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF
      have hsq := (GlobalTheory.BadShare.good_iff.1 hG).1
      have hc : ∀ v, ∃ c : Fin N → ZMod g, Formalism.CyclotomicNorms.monicOf c = F v := by
        intro v
        have hv := hsq v
        rw [GlobalTheory.BadShare.sqSet_eq_monicOf, Finset.mem_filter, Finset.mem_image] at hv
        obtain ⟨c, -, hc⟩ := hv.1
        exact ⟨c, hc⟩
      choose a ha using hc
      have hMa : (fun v => Formalism.CyclotomicNorms.monicOf (a v)) = F := funext ha
      refine ⟨a, ?_, hMa⟩
      rw [hMa]
      exact hG
    · rintro ⟨a, hG, rfl⟩
      exact GlobalTheory.BadShare.mem_goodSet_iff_good.2 hG
  rw [hset, Finset.sum_image (fun a _ b _ e => hinj e), Finset.sum_filter]

theorem sum_sigma_two {P : Fin 2 → Type} {A : Fin 2 → Type} [Fintype (∀ kv : (Σ k : Fin 2, P k), A kv.1)]
    [Fintype (P 0 → A 0)] [Fintype (P 1 → A 1)] (f0 : (P 0 → A 0) → ℂ) (f1 : (P 1 → A 1) → ℂ) :
    (∑ a : (∀ kv : (Σ k : Fin 2, P k), A kv.1), f0 (fun v => a ⟨0, v⟩) * f1 (fun v => a ⟨1, v⟩)) =
      (∑ a, f0 a) * ∑ b, f1 b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.piCurry fun (k : Fin 2) (_ : P k) => A k).trans
    (piFinTwoEquiv fun k => P k → A k)) _ _ (fun a => rfl)

theorem goodProjector_coeff_eq_prod_at_two_typePrimes : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  intro D τ hτ γ
  classical
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
    unfold NTypes.e0
    rfl
  let f : ∀ k : Fin 2, (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) → ℂ := fun k b =>
    if GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (b v)) then
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (b v))).coeff (γ ⟨k, v⟩) else 0
  have hsplit : ∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
        f 0 (fun v => a ⟨0, v⟩) * f 1 (fun v => a ⟨1, v⟩) := by
    intro a
    have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
        ∀ k : Fin 2, GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
      unfold NTypes.goodTuple GlobalTheory.BadShare.Good
      exact Iff.rfl
    rw [Fintype.prod_sigma, Fin.prod_univ_two]
    by_cases h0 : GlobalTheory.BadShare.Good (D.host.g 0) D.R.r (D.nd.chiT 0) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
      by_cases h1 : GlobalTheory.BadShare.Good (D.host.g 1) D.R.r (D.nd.chiT 1) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
      simp [f, hg, Fin.forall_fin_two, h0, h1]
  have hk : ∀ k : Fin 2, ∑ b, f k b = GlobalTheory.BadShare.eGood (fun _ => τ k) (D.nd.chiT k) (fun v => γ ⟨k, v⟩) := by
    intro k
    refine (Eq.trans ?_ (sum_good (g := D.host.g k) (N := D.R.r) (D.nd.chiT k)
      (fun F => ∏ v, (D.ntypes.eSer k (F v)).coeff (γ ⟨k, v⟩)))).trans ?_
    · rfl
    · unfold GlobalTheory.BadShare.eGood
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun F hF => ?_)
      have hsq := (GlobalTheory.BadShare.good_iff.1 (GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF)).1
      unfold GlobalTheory.BadShare.tens
      exact Finset.prod_congr rfl fun v _ => hτ k (F v) (hsq v) (γ ⟨k, v⟩)
  rw [he, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ hsplit,
    sum_sigma_two (P := fun k => D.nd.PlG k) (A := fun k => Fin D.R.r → ZMod (D.host.g k)) (f 0) (f 1), hk 0, hk 1]

end GlobalTheory.GoodProjProd

end
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift : ∀ (n : ℕ) (c : ℤ) (lam lam' : DomWeight n), (∀ i, lam'.w i = lam.w i + c) → Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  first | exact @GlobalTheory.OneFunctional.iso_twist_det_irr_shift | exact GlobalTheory.OneFunctional.iso_twist_det_irr_shift | (intros; apply GlobalTheory.OneFunctional.iso_twist_det_irr_shift <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.contracts_tensorProduct_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  first | exact @GlobalTheory.OneFunctional.contracts_chain | exact GlobalTheory.OneFunctional.contracts_chain | (intros; apply GlobalTheory.OneFunctional.contracts_chain <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.iso_dual_outer_outer_dual : ∀ (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)), Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_outer_dual | exact GlobalTheory.OneFunctional.iso_outer_dual | (intros; apply GlobalTheory.OneFunctional.iso_outer_dual <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.iso_unitaryIrrep_conj_dual : ∀ (n : ℕ) (lam : DomWeight n), Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  first | exact @GlobalTheory.ConjDual.iso_conj_dual | exact GlobalTheory.ConjDual.iso_conj_dual | (intros; apply GlobalTheory.ConjDual.iso_conj_dual <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.contracts_of_iso_directSum' : ∀ (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i)) (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I), Iso (Representation.directSum fun i => Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ → (∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥) → Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1 → Contracts φ σ (b i₀) := by
  first | exact @GlobalTheory.OneFunctional.contracts_of_iso_directSum | exact GlobalTheory.OneFunctional.contracts_of_iso_directSum | (intros; apply GlobalTheory.OneFunctional.contracts_of_iso_directSum <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.exists_ganGrossPrasad_column_weights : ∀ (S : Sizes) (Q : Entries S), Q.Good → ∃ kap : ∀ i : Fin (S.m + 1), DomWeight (S.nC i), (∀ r, (kap 0).dual.w r = hw Q.basePar r) ∧ (∀ r, (kap (Fin.last _)).dual.w r = hw Q.smallPar r) ∧ ∀ i : Fin S.m, StepW (Q.c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (-Q.c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (kap i.castSucc) (kap i.succ) := by
  first | exact @GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | exact GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights | (intros; apply GlobalTheory.OneFunctional.ColumnWeights.exists_column_weights <;> assumption)
end
