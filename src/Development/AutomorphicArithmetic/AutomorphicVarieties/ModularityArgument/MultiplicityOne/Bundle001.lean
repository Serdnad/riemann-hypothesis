module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockGA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Mult

def NoData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, ¬ D.Has π → D.Reg →
    (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) →
    ¬ ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def GeomTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → dimW lam ≠ 0 ∧
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
      trOn (forms S lam K') (hop S K' f) = dimW lam * geomU S lam f

def LevTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K'' → (∀ w, K'' w ≤ K' w) →
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → trOn (forms S lam K'') (hop S K'' f) = trOn (forms S lam K') (hop S K' f)

def EvalD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ w ∉ Z, K' w = KL n w) → ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (t : ι → ∀ w : Pl E, SmIrr (GLw n w)) (B : ι → Pl E → Multiset ℂˣ),
      (∀ i, (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU (σ i) w) ∧ (∀ w ∈ Z, Cp (σ i) w (t i w)) ∧
        ∀ w, Off Z w → IsSplitAt w → ∃ τ, Cp (σ i) w τ ∧ HasSatGL w τ.ρ (B i w)) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧
        trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ∑ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w (n := n)) (f w)) * val1 T e₁ e₂ (B i) ^ k

def CpUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ w, IsSplitAt w →
  ∀ τ τ' : SmIrr (GLw n w), Cp σ w τ → Cp σ w τ' →
    (∀ B, HasSatGL w τ.ρ B → HasSatGL w τ'.ρ B) ∧ ∀ f, trc τ.ρ (KGL w (n := n)) f = trc τ'.ρ (KGL w (n := n)) f

def LevInd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) → K ≤ KL n w →
  ∃ f : GLw n w → ℂ, Lc (KGL w (n := n)) f ∧ (∀ K₁ ≤ K, IsHecke K₁ fun x : UL n w => f x.1) ∧
    ∀ τ : SmIrr (GLw n w), fixed (τ.ρ.comp (UL n w).subtype) K ≠ ⊥ → trc τ.ρ (KGL w (n := n)) f ≠ 0

def LcLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ f : GLw n w → ℂ, Lc (KGL w (n := n)) f →
  ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ IsHecke K fun x : UL n w => f x.1

def ChoiceM : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S →
  ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
  ∃ (Z : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (w₀ : Pl E) (f₀ : GLw n w₀ → ℂ),
    SplitIn S Z ∧ (∀ w ∈ S, w ∉ Z → K' w = KL n w) ∧ (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) ∧
    (∀ w ∈ Z, π.IsLocComp w (τ w)) ∧ w₀ ∈ Z ∧ Lc (KGL w₀ (n := n)) f₀ ∧ trc (τ w₀).ρ (KGL w₀ (n := n)) f₀ ≠ 0 ∧
    ∀ y, f₀ y ≠ 0 → y.val.charpoly.Separable

def OffSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), (∀ w ∈ S, K' w = K'' w) →
  globLev S K' = globLev S K''

def CountAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (J : Type) (_ : Fintype J) (C : J → Pl E → Multiset ℂˣ),
      (∀ j, ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C j w).card = n ∧ C j w ≠ B w) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂, val1 T e₁ e₂ B = 1 → (∀ j, val1 T e₁ e₂ (C j) = 0) →
        ∀ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧ (1 ≤ k → trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ((Nat.card {i // At π (σ i)} : ℂ) * ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) (f w)))

def RCountAt : Prop := CompOf → EvalD → CpUniq → Places → CountAt

def Ident : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ lam : InfinitePlace E → DomWeight n, ∃ a : ℝ, 0 < a ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (f : ∀ w : Pl E, GLw n w → ℂ),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) →
    (∀ w ∈ Z, π.IsLocComp w (τ w) ∧ Lc (KGL w (n := n)) (f w) ∧ trc (τ w).ρ (KGL w (n := n)) (f w) ≠ 0) →
    (∃ w ∈ Z, ∀ y, f w y ≠ 0 → y.val.charpoly.Separable) →
    ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ → (Nat.card {i // At π (σ i)} : ℝ) = a

def RIdent : Prop := NoData → CountAt → GeomTr → G2s → MatchUnit → MatchSplit → EndoBlockS → StableBlockSA → Ident

def RMult : Prop := Ident → CountAt → LevTr → GeomTr → LevInd → LcLev → ChoiceM → OffSec → MuEx → Mult

end UpperTheory.V.Z.Mult
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.stableSA :
    Enlarge → Places → StableBlockGA → StableBlockSA := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn l₁ l₂
  obtain ⟨c₀, hc₀, hl⟩ := hG E hunr n hn l₁ l₂
  refine ⟨c₀, hc₀, fun π hreg hd hinf S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl π hreg hd hinf S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end
