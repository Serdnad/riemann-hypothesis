module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle298
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle299
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → ρ.Is → A.Forms → ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β, (∀ y, IsContAut (c.X j) (t.rd j β ψ y)) ∧ (∀ y g (κ : A.U j β), t.rd j β ψ y (g * κ.1) = (A.chi j β κ : ℂ) * t.rd j β ψ y g) ∧ (∀ y y' g, ∀ k ∈ GinfC (c.X j), IsTr (ρ.r j hj k) (ρ.fr j y) (ρ.fr j y') → t.rd j β ψ y (g * k) = t.rd j β ψ y' g) ∧ ∀ g, (fun z => t.rd j β ψ ((ρ.fr j).symm z) g) ∈ ValC _ (ρ.lam j) := by
  first | exact @GlobalTheory.SeeSaw.scalarForm_laws | exact GlobalTheory.SeeSaw.scalarForm_laws | (intros; apply GlobalTheory.SeeSaw.scalarForm_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_iteratedIntegrand_vacuumForm_base_points : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂, ∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∀ (φ : t.Ch j → GA D (c.X j) → ℂ) (F : GA D (c.V (j + 1 + 1)) → ℂ) Ψ₁ Ψ₂ f z, Ψ₁ = v.Ψ j P₁ 1 a → Ψ₂ = v.Ψ (j + 1) P₂ a a' → f = rTrans (a' * v.b (j + 1 + 1)) F → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => t.integrand j σ h P₁ P₂ φ F (a * q₁.1) (a' * q₂.1)) (w.sc j * w.sc (j + 1) * z) := by
  first | exact @GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt | exact GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt | (intros; apply GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  exact GlobalTheory.VReal.v_real
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  first | exact @GlobalTheory.ThetaMap.thetaMap | exact GlobalTheory.ThetaMap.thetaMap | (intros; apply GlobalTheory.ThetaMap.thetaMap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.lastKernelDatum_in_lastLineFrame_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  exact @GlobalTheory.SeeSaw.lastKernel_reps
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel

namespace GlobalTheory.LatPresc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem latV_eq_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) = latV S L' (· = v) :=
  le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLat_congr {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    {L L' : Lat S} (h : latV S L (· = p.v) = latV S L' (· = p.v)) (Λ : Submodule 𝒪[k] (n → k)) :
    β.IsLat L Λ ↔ β.IsLat L' Λ := by
  unfold Frame.IsLat
  rw [h]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i ∈ l, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k (p i) S n (β i) M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩
    · by_cases e : i' = i
      · subst e; exact h3
      · have hne : (p i').v ≠ (p i).v := fun e' => e (hp e')
        exact (isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2
          (h1 i' ((List.mem_cons.1 hi').resolve_left e))
    · exact (latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans
        (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))

theorem latAll : ∀ D : D7, LatAll D := by
  intro D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ
  obtain ⟨M, hM, h1, h2⟩ := exists_modify hP.inj α Λ hΛ hL I
  exact ⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩

end GlobalTheory.LatPresc
end

section

open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_idele_change_finitely_many_split_places : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ h : D.host.E, h ≠ 0 → star h = h → ∀ m : (AE D)ˣ, ∃ m' : (AE D)ˣ, (∀ x, ¬ P x → ∀ a ∈ idAt D (· = x), (m' : AE D) * a = (m : AE D) * a ∧ cA D (m' : AE D) * a = cA D (m : AE D) * a) ∧ ∀ x, P x → ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (m' : AE D) * cA D (m' : AE D) * incA D h * a ∈ intAt D (· = x) := by
  first | exact @GlobalTheory.FinPl.exists_idele_change_split | exact GlobalTheory.FinPl.exists_idele_change_split | (intros; apply GlobalTheory.FinPl.exists_idele_change_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  first | exact @GlobalTheory.HalfGen.latO_le_closure_halves | exact GlobalTheory.HalfGen.latO_le_closure_halves | (intros; apply GlobalTheory.HalfGen.latO_le_closure_halves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  first | exact @GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | exact GlobalTheory.FinPl.UnitPlaces.latA_eq_latV | (intros; apply GlobalTheory.FinPl.UnitPlaces.latA_eq_latV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineProjection_mem_homLatticeCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  first | exact @GlobalTheory.LineProj.lineProj_mem_latO | exact GlobalTheory.LineProj.lineProj_mem_latO | (intros; apply GlobalTheory.LineProj.lineProj_mem_latO <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  first | exact @GlobalTheory.LastVacPf.lastVac | exact GlobalTheory.LastVacPf.lastVac | (intros; apply GlobalTheory.LastVacPf.lastVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
end
