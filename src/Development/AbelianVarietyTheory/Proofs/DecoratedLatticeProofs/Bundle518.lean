module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle307
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle943
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.AbsPointwiseMonoConstant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle288
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle458
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle452
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle413
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VertexAllProof

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem over_self {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] {α : Frame p S m'} {β : Frame p T m}
    {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ} (h : Over ψ α β LS LT g Φ f) (hU : p.UnitAA)
    (ΛS : Submodule 𝒪[k] (m' → k)) (ΛT : Submodule 𝒪[k] (m → k)) (hLS : α.IsLat LS ΛS) (hLT : β.IsLat LT ΛT) :
    Over ψ α β LS LT g (latInd ΛS ΛT) g := by
  obtain ⟨hS, hT, hvac, -, ⟨Tm, hTm⟩, -⟩ := h
  have hE := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p m m' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
  refine ⟨hS, hT, hvac, GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat D k p m m' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
  have hv := hT'.vac
  rw [one_smul] at hv
  change g = T' (extFun α β (latInd ΛS ΛT))
  rw [hE, hv]

theorem overAll_nil {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type}
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n}
    {LS : Lat S} {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

end GlobalTheory.FinPl.VertexAllProof


open GlobalTheory.FinPl.VertexAllProof in
theorem GlobalTheory.FinPl.vertexAll : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  intro D k _ _ _ _ ι p I P hPl q ψ χ hχ hc
  have hvg := fun i => GlobalTheory.T.gluedPlace_doubleStep_exact_signed_constant D k (p i) q ψ (χ i) (hχ i) (hc i)
  refine ⟨fun i => (hvg i).choose, fun i => (hvg i).choose_spec.1, ?_⟩
  intro n n' n'' _ _ _ _ _ _
  have hrc := fun i => (hvg i).choose_spec.2 n n' n''
  choose r e hr hre using hrc
  refine ⟨r, e, hr, ?_⟩
  intro σ B J B' s₁ s₂ l vL hunr a b a' M₀ M₁ M₂ _ _ _ hgl Ξ₁ Ξ₂ _ _
  have hP : ∀ i, P (p i).v := fun i => (hPl.mem _).2 ⟨i, rfl⟩
  have hmaps : ∀ (ls : List ι) (φ : GA D B.A → ℂ), a.Ram φ →
      a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) := fun ls φ hφ =>
    (GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D k ι p q χ hχ (fun i => (hvg i).choose) n' B.A B.V₀ a hPl.inj ls).1.mapsTo hφ
  have hV : ∀ ls : List ι, ∀ Ξ₁' Ξ₂',
      OverAll ψ a.α₀ b.β M₀ M₁ (fun i => tensCol (phiOne (a.P i) (b.Q i)) (vecInd (b.Q i).lat)) ls Ξ₁ Ξ₁' →
      OverAll ψ b.β a'.α₀ M₁ M₂ (fun i => tensRow (phiOne (b.Q i) (a'.P i)) (dualInd (b.Q i).lat)) ls Ξ₂ Ξ₂' →
      ∀ φ, a.Ram φ → hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
        (ls.map fun i => (r i : ℂ) * chrPow s₁.χW ((p i).idele q.unit) (e i)).prod •
          hand0 s₁ s₂ l vL (a.sAll q (fun i => resChar (χ i) (hχ i) q) (fun i => (hvg i).choose) ls φ) Ξ₁' Ξ₂' := by
    intro ls
    induction ls with
    | nil =>
      intro Ξ₁' Ξ₂' h1 h2 φ _
      rw [overAll_nil.1 h1, overAll_nil.1 h2, List.map_nil, List.prod_nil, one_smul]
      rfl
    | cons i ls ih =>
      intro Ξ₁' Ξ₂' h1 h2 φ hφ
      obtain ⟨g₁, hg₁, hΞ₁'⟩ := overAll_cons.1 h1
      obtain ⟨g₂, hg₂, hΞ₂'⟩ := overAll_cons.1 h2
      have ho₁ := over_self hΞ₁' (hgl i).1.unit _ _ (hgl i).1.lat (hgl i).2.2
      have ho₂ := over_self hΞ₂' (hgl i).1.unit _ _ (hgl i).2.2 (hgl i).2.1.lat
      obtain ⟨F, hF, hFP⟩ := (hmaps ls φ hφ).2 i
      have hv := hre i (a.P i) (b.Q i) (a'.P i) σ B J B' s₁ s₂ l vL (hunr _ (hP i)).1 (hunr _ (hP i)).2 (a.α i)
        (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (hgl i).1.sum (hgl i).2.1.sum M₀ M₁ M₁ M₂ g₁ g₁ Ξ₁' g₂ g₂ Ξ₂' ho₁ hΞ₁'
        ho₂ hΞ₂' F hF
      have hsop := ((GlobalTheory.T.ramifiedOperator_bijective_finite_translation_combination D k (p i) n' q (χ i) (hχ i) _ rfl ((hvg i).choose) B.A (a.α i) (a.P i)).2.1 F hF).2
      rw [ih g₁ g₂ hg₁ hg₂ φ hφ, ← hFP, hv, ← hsop, hFP, smul_smul, List.map_cons, List.prod_cons, mul_comm]
      rfl
  intro Ξ₁' Ξ₂' h1 h2 φ hφ
  exact hV I Ξ₁' Ξ₂' h1 h2 φ hφ
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.ShapeExProof

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem places {v : VCom c} {o : TDat c k ι} (hpre : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨hpre.nodup, hpre.all, hpre.inj, hpre.tP, fun i => (hpre.char i).2⟩

theorem gluedCore_congr {ρ : ℕ} {B : BesLev D ρ} {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {L L' : Lat B.V₀}
    {q : Unif k} {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n}
    (hL : latV B.V₀ L' (· = p.v) = latV B.V₀ L (· = p.v)) (g : GluedCore B L q β β₀ P) : GluedCore B L' q β β₀ P :=
  ⟨g.unit, g.sum, g.norm, fun y => by rw [hL]; exact g.lat y⟩

end GlobalTheory.SeeSaw.ShapeExProof

namespace GlobalTheory.SeeSaw.ShapeExProof

theorem shapeEx : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  intro D c v k _ _ _ _ ι o hc hdisj hNT hpre hNv hgP hLZ
  obtain ⟨N0, M0, β₀, hN0, hgood0, hsplit0, hglued0⟩ := GlobalTheory.T.exists_lattices_goodPosition_all_places D c v k ι o hc hNT hpre hLZ
  have key : ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ x, GoodAt { v with N := N } { o with M := M } x) ∧
      (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M } x) ∧
      (∀ j ρ h, ∀ x, x ∉ v.gP → latV _ (M j ρ h) (· = x) = latV _ (M0 j ρ h) (· = x)) := by
    rcases v.gP.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
    · refine ⟨N0, M0, fun j hj => ⟨hN0 j hj, fun x hx => by simp [hE] at hx⟩, fun j ρ h x hx => by simp [hE] at hx,
        fun x => ⟨(hgood0 x).1, (hgood0 x).2⟩, fun x hx => ⟨(hsplit0 x hx).1, (hsplit0 x hx).2⟩, fun _ _ _ _ _ => rfl⟩
    · have hsdM : ∀ j ρ h, IsSelfDualC _ (o.M j ρ h) := fun j ρ h => ((hgP x0 hx0).1.bf j ρ h).sdV₀
      have hsdM0 : ∀ j ρ h, IsSelfDualC _ (M0 j ρ h) := fun j ρ h => ((hgood0 x0).bf j ρ h).sdV₀
      have hpN : ∀ j, ∃ L : Lat (c.V j), j < D.R.m → (IsSelfDualC (c.V j) L ∧
          (∀ x ∈ v.gP, latV (c.V j) L (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV (c.V j) L (· = x) = latV (c.V j) (N0 j) (· = x)) := by
        intro j
        by_cases hj : j < D.R.m
        · obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.T.exists_selfDual_lattice_patched_at_places D (c.V j) (N0 j) (v.N j) (hN0 j hj) (hNv j hj) v.gP
          exact ⟨L, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨N0 j, fun h => absurd h hj⟩
      choose N hN using hpN
      have hpM : ∀ j ρ h, ∃ L : Lat (c.bes j ρ h).V₀, IsSelfDualC _ L ∧
          (∀ x ∈ v.gP, latV _ L (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV _ L (· = x) = latV _ (M0 j ρ h) (· = x) := fun j ρ h =>
        GlobalTheory.T.exists_selfDual_lattice_patched_at_places D _ (M0 j ρ h) (o.M j ρ h) (hsdM0 j ρ h) (hsdM j ρ h) v.gP
      choose M hM using hpM
      have hat : ∀ x, (x ∈ v.gP → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x)) ∧
          (x ∉ v.gP → (GoodAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → SplitAt { v with N := N } { o with M := M } x)) := by
        intro x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c v k ι o N M x (fun j hj => ⟨hNv j hj, (hN j hj).1, (hN j hj).2.1 x hx⟩)
            (fun j ρ h => ⟨hsdM j ρ h, (hM j ρ h).1, (hM j ρ h).2.1 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c { v with N := N0 } k ι { o with M := M0, β₀ := β₀ } N M x
            (fun j hj => ⟨hN0 j hj, (hN j hj).1, (hN j hj).2.2 x hx⟩)
            (fun j ρ h => ⟨hsdM0 j ρ h, (hM j ρ h).1, (hM j ρ h).2.2 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
      refine ⟨N, M, fun j hj => ⟨(hN j hj).1, (hN j hj).2.1⟩, fun j ρ h => (hM j ρ h).2.1, fun x => ?_, fun x hxT => ?_,
        fun j ρ h => (hM j ρ h).2.2⟩
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).1 (hgP x hx).1
        · exact ((hat x).2 hx).1 (hgood0 x)
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).2 (hgP x hx).2
        · exact ((hat x).2 hx).2 (hsplit0 x hxT)
  obtain ⟨N, M, hN, hM, hgood, hsplit, hoff⟩ := key
  have hd : ∀ j, ∃ d : WO (c.X j) (c.X (j + 1)) →₀ ℂ, CombAt (· ∈ v.tP) d ∧ (j < D.R.m → ∀ f,
      Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
      OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
        (comb c.ψ _ _ d f)) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨d, hdc, hdr⟩ := ((GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D) k ι o.p o.I (· ∈ v.tP) (places hpre) (Fin (c.X (j + 1)).rank)
        (Fin (c.X j).rank) c.ψ hc.std (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L
        (hc.x j hj.le).sd (hc.x (j + 1) hj).sd (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).1 (fun i => GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)
      exact ⟨d, hdc, fun _ => hdr⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hj⟩
  choose dT hdC hdR using hd
  have hpT : ∀ i, (o.p i).v ∉ v.gP := fun i hg =>
    Finset.disjoint_left.mp hdisj hg ((hpre.tP _).mpr ⟨i, rfl⟩)
  refine ⟨N, dT, M, β₀, hN, hM, hdC, ⟨⟨hpre.1, hpre.2, hpre.3, hpre.4, hpre.5, hpre.6, hpre.7, hpre.8, hpre.9, hpre.10, hpre.11⟩,
    fun x => ⟨(hgood x).1, (hgood x).2⟩, fun x hx => ⟨(hsplit x hx).1, (hsplit x hx).2⟩,
    fun j ρ h i => gluedCore_congr (hoff j ρ h _ (hpT i)) (hglued0 j ρ h i), fun j hj => hdR j hj, fun j => rfl⟩⟩

end GlobalTheory.SeeSaw.ShapeExProof
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCoefSplit




theorem actO_inf : ∀ (D : D7) (S T : HSp D) (a : GA D S) (b : GA D T), a ∈ GinfC S → b ∈ GinfC T →
    ∀ w : WO S T, w.map (infPart D) = 0 → actO S T a b w = w := by
  intro D S T a b ha hb w hw
  have hfb : (Formalism.L2.Theta.mt T b).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hb)
    exact h
  have hfa : (Formalism.L2.Theta.mt S a⁻¹).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 (Subgroup.inv_mem _ ha))
    exact h
  have h0 : ∀ k j, infPart D (w k j) = 0 := fun k j => by
    have := congrFun (congrFun hw k) j
    simpa using this
  have e1 : Formalism.L2.Theta.mt T b * w = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T b i k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hfb i) k
        simpa [Matrix.one_apply] using this

      rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  have e2 : w * Formalism.L2.Theta.mt S a⁻¹ = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt S a⁻¹ k j) = if k = j then 1 else 0 := fun k => by
        have := congrFun (congrFun hfa k) j
        simpa [Matrix.one_apply] using this

      rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  unfold actO
  rw [e1, e2]

open GlobalTheory.VacPairSchur GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem om_heisO_inf {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {a : GA D S} (ha : a ∈ GinfC S) {b : GA D T} (hb : b ∈ GinfC T)
    {w : WO S T} (hw : w.map (infPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (a, b) (heisO ψ S T w f) = heisO ψ S T w (om (a, b) f) := by
  rw [hom.om_heis a b w f hf, actO_inf D S T a b ha hb w hw]

theorem fockVac_om_fin {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T} (hy : y ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (x, y) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      compAt θ τ (Formalism.L2.Theta.mt T y) * z * compAt θ τ (Formalism.L2.Theta.mt S x⁻¹) = z := fun z => by
    rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (Subgroup.inv_mem _ hx),
      Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (x, y)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem om_fin_pureTensorO {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T}
    (hy : y ∈ GfC T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (x, y) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT x y
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.one_mul]) f hf P).2

theorem l2_eq_star (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    l2 μ 𝓕 f g = star (thetaIP μ 𝓕 f g) := by
  unfold l2 Formalism.IndefR.Lift.pet thetaIP
  change _ = (starRingEnd ℂ) (∫ w in 𝓕, star (f w) * g w ∂μ)
  rw [← integral_conj]
  congr 1
  funext w
  simp [mul_comm]

theorem pair_eq_inf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv a ha b hb P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (z : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (z • f + f') g = star z * Φ f g + Φ f' g := by
    intro z f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hf hf' P, map_add (f := _), map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul z (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (z : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (z • g + g') = z * Φ f g + Φ f g' := by
    intro z f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul z (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hbd : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_inf hom ha hb hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact GlobalTheory.T.schur_finiteHeisenberg_fockVacuumThetaFunctions D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hbd hi

end GlobalTheory.FockCoefSplit

namespace GlobalTheory.FockCoefSplit

open GlobalTheory.RawLift

theorem coef_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ pS pT : D.what₂.Tau → ℕ, (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q)) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ x ∈ GfC S, ∀ y ∈ GfC T, ∀ Q Q', l2 μ 𝓧 (om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 f f = l2 μ 𝓧 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 (om (x, y) f) f := by
  intro D ψ θ S T χS χT om hθ hom μ 𝓧 hcv sS BS sT BT hcS hcT pS pT hoS hoT f hf hvf hpt a ha b hb x hx y hy Q Q'
  obtain ⟨c, hc⟩ := pair_eq_inf D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓧 hcv a ha b hb Q Q'
  have hx' : x⁻¹ ∈ GfC S := Subgroup.inv_mem _ hx
  have hy' : y⁻¹ ∈ GfC T := Subgroup.inv_mem _ hy
  have hg : IsThetaFunO ψ S T (om (x⁻¹, y⁻¹) f) := hom.om_pres _ _ hf
  have hvg : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x⁻¹, y⁻¹) f) :=
    fun τ => fockVac_om_fin hom hθ hx' hy' τ _ hf (hvf τ)
  have inv : ∀ A B : WO S T → ℂ, IsThetaFunO ψ S T A → IsThetaFunO ψ S T B →
      thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) := by
    intro A B hA hB
    have e : om (x, y) (om (x⁻¹, y⁻¹) B) = B := by
      rw [← Module.End.mul_apply, ← map_mul,
        show ((x, y) * (x⁻¹, y⁻¹) : GA D S × GA D T) = 1 from mul_inv_cancel (x, y), map_one, Module.End.one_apply]
    calc thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 (om (x, y) A) (om (x, y) (om (x⁻¹, y⁻¹) B)) := by rw [e]
      _ = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) :=
        GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hom hcv _ _ _ hA (hom.om_pres _ _ hB)
  have e1 : om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      om (x, y) (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) := by
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  simp only [l2_eq_star]
  rw [← star_mul', ← star_mul']
  congr 1
  rw [e1, inv _ _ (hom.om_pres _ _ (hpt Q)) (hpt Q'), om_fin_pureTensorO hom hθ sS BS sT BT hx' hy' hf Q',
    hc f _ hf hg hvf hvg, inv _ _ hf hf, hc f f hf hf hvf hvf]
  ring

end GlobalTheory.FockCoefSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (k : Fin D.R.m) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ), S = parB (Ptw D) k → S' = parB (Ptw D) (k + 1) → IsInfFam θ → ChainPar D k → IsWeilExp ψ V W (expS D k) (expT D k) ω → IsVacVec ψ θ M M' f → ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∃ T : PolF D W.rank V.rank → SmT M → SmT M', (∀ P v, T P v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v})) ∧ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = T P v} ∧ LiftsM θ M M' ν 𝓕 (fun P h g => conj (thetaKO ω g h (ptOf ψ θ M M' f P))) T := by
  first | exact @GlobalTheory.Corev.LiftUp.liftUp_mult | exact GlobalTheory.Corev.LiftUp.liftUp_mult | (intros; apply GlobalTheory.Corev.LiftUp.liftUp_mult <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AbsRecGap

theorem abs_all_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Formalism.MainNotions.BridgeLemma.AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cn C := by
  intro Cg cb Cu cT CT C0
  have hG : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.AmpMomentsGap.amplitude_moments_gap hG Cg cb Cu cT CT C0 1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRangeUniform.abs_range_constants_first Cg cb Cu cT CT 1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, le_max_right _ _, fun Cn => ?_⟩
  obtain ⟨m₂, hM⟩ := hMo Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max (max m₁ m₂) 1000)
  refine ⟨thr, ?_⟩
  intro D large₂ C' Cl hC' hCl τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
  have h0 : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := by
    unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
  obtain ⟨h1000, -, hm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl h0.1
  have hm1000 : (1000 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hm
  have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1000 → GlobalTheory.Amp.Big D large₂ Cl m₀ :=
    fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
  exact (hAbs' Cn D large₂ C' Cl C0 (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
    (hM D large₂ C' Cl h1000 (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
    h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2

end GlobalTheory.AbsRecGap
end
