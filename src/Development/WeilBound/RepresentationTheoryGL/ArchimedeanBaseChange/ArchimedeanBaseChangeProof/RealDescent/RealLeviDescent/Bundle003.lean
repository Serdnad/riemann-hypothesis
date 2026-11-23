module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.SecondLeviFamily
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle001
public import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ComplexConjugate

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


variable (E n) in
def infAt (w : InfinitePlace E) : GA E n →* PositivityTheory.RgTw.G n :=
  Matrix.GeneralLinearGroup.map ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).comp (pInf E))


variable (E n) in
def finOf : GA E n →* GL (Fin n) (Af E) := Matrix.GeneralLinearGroup.map (pFin E)


variable (E n) in
def thetaF (g : GL (Fin n) (Af E)) : GL (Fin n) (Af E) := finOf E n (thetaA E n (finGL E n g))

def IsHeckeF (K : Subgroup (GL (Fin n) (Af E))) (h : GL (Fin n) (Af E) → ℂ) : Prop :=
  HasCompactSupport h ∧ ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, h (k₁ * g * k₂) = h g

def heckeOp [MeasurableSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E))) (h : GL (Fin n) (Af E) → ℂ)
    (φ : GA E n → ℂ) : GA E n → ℂ :=
  fun x => ∫ g, h g * φ (x * finGL E n g) ∂μf

def phiProd (lam : InfinitePlace E → Fin n → ℤ)
    (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
    (h : GL (Fin n) (Af E) → ℂ) (y : H E n 0) : ℂ :=
  (∏ w, PositivityTheory.RgBcC.phiOf (PositivityTheory.RgBcC.lefE n (lam w)) (PositivityTheory.RgBcC.lefT n (lam w)) (k w) (infAt E n w y.1)) *
    h (finOf E n y.1)

def ThetaFixedGlobalCharacter : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
    ThetaFix π → ∀ lam : InfinitePlace E → Fin n → ℤ, (∀ w, Antitone (lam w)) →
    (∀ w, HasInfCharGL π.V w.embedding (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding)
        (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) false) Finset.univ.val)) →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ) →
    ∀ [MeasurableSpace (PositivityTheory.RgTw.G n)] [BorelSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
      [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
      (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (μ : Measure (H E n 0)) [μ.IsHaarMeasure],
    ∃ (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y) (c : ℂ),
      Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ y ∈ Y, ∀ k ∈ K, finRep E n k y = y) ∧
      (∀ h, IsHeckeF K h → ∀ y : Y, (((ρ h y : Y) : Sm E n) : GA E n → ℂ) = heckeOp μf h ((y : Sm E n) : GA E n → ℂ)) ∧
      (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      A * A = 1 ∧ (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ c ≠ 0 ∧
      ∀ (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lam w)) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μ π (phiProd lam k h) (c * (∏ w, val w (PositivityTheory.RgBcC.infOf (lam w))) * LinearMap.trace ℂ Y (ρ h * A))

end PositivityTheory.Rg.BcB.Desc

end
end

section

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

theorem isLev_id (lam : Fin n → ℤ) : IsLev lam fun a => ((a : Fin n) : ℕ) := ⟨fun _ _ h => h, fun _ _ h => congrArg lam (Fin.ext h)⟩

theorem mem_harmSet {lam : Fin n → ℤ} {μ : Fin n → ℝ} (h : μ ∈ harmSet lam) :
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ μ = muQ lam fun a => (l a : ℕ) := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} (lev : Fin n → Fin n) (h : IsLev lam fun a => (lev a : ℕ)) :
    muQ lam (fun a => (lev a : ℕ)) ∈ harmSet lam := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lev, h, rfl⟩

def Compress : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ muQ lam (fun a => (l a : ℕ)) = muQ lam lev

theorem multG_of (hCp : Compress) (hM : MultFor) (hA : AdmLeast) (h1 : N1) (hC : ConeWeightsNotSecondType) (hE : ModelEx) (h7 : KTypeGenerationHighest) : MultG := by
  intro n lam hl V _ _ E1 E2 σ A hc
  classical
  have hne_h : (harmSet lam).Nonempty := ⟨_, muQ_mem_harmSet (fun a => a) (isLev_id lam)⟩
  by_cases hex : ∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥
  swap
  · push_neg at hex
    obtain ⟨μ₀, hμ₀⟩ := hne_h
    refine ⟨μ₀, hμ₀, fun μ hμ _ => hex μ hμ, ?_⟩
    intro v w hv _ hv0
    rw [hex μ₀ hμ₀, Submodule.mem_bot] at hv
    exact absurd hv hv0
  obtain ⟨μ₁, hμ₁, hne₁⟩ := hex
  let S := (harmSet lam).filter (fun μ => hwSp E1 E2 μ ≠ ⊥)
  have hSne : S.Nonempty := ⟨μ₁, Finset.mem_filter.mpr ⟨hμ₁, hne₁⟩⟩
  obtain ⟨μ₀, hμ₀S, hmin⟩ := S.exists_min_image (fun μ => nsq (μ + rhoV n)) hSne
  obtain ⟨hμ₀, hne₀⟩ := Finset.mem_filter.mp hμ₀S
  obtain ⟨l0, hl0, rfl⟩ := mem_harmSet hμ₀
  have hadm : AdmFor lam (fun a => (l0 a : ℕ)) E1 E2 := by
    refine hA n lam hl V E1 E2 σ A hc _ hl0 hne₀ ?_
    intro lev' hlev' hne'
    obtain ⟨l', hl', heq⟩ := hCp n lam lev' hlev'
    have hmem : muQ lam lev' ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hne'⟩
      rw [← heq]
      exact muQ_mem_harmSet l' hl'
    exact hmin _ hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₀
  refine ⟨_, hμ₀, ?_, ?_⟩
  · intro μ hμ hμne
    by_contra hb
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨M⟩ := hE n lam hl _ hl0
    have hMn2 : ∀ ν, IsSecondTypeWeight lam (fun a => (l0 a : ℕ)) ν → hwSp M.F1 M.F2 ν = ⊥ := by
      intro ν hν
      letI := M.nacg
      letI := M.ips
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact hC n lam hl _ hl0 ν (M.cone ν y hy hy0) hν
    obtain ⟨a, ha, hav⟩ := hc.irr v x hv0
    have hcone := h7 hM n lam hl _ hl0 V E1 E2 hc.pair hadm M hMn2 v hv hv0 μ x hx hx0 ⟨a, ha, hav⟩
    obtain ⟨l', hl', rfl⟩ := mem_harmSet hμ
    exact hμne (h1 n lam hl _ _ hl0 hl' hcone)
  · intro v' w hv' hw hv'0
    obtain ⟨a, ha, hav⟩ := hc.irr v' w hv'0
    exact hM n lam hl _ hl0 V E1 E2 hadm v' w hv' hw hv'0 ⟨a, ha, hav⟩

end PositivityTheory.RgBcC.RealD
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def domC (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort (fun a => -x a)

def spinSq (ν : Fin n → ℝ) : ℝ := nsq (domC (ν - rhoV n) + rhoV n)

def LSq (lam : Fin n → ℤ) : ℝ := nsq fun a => 2 * ((lam a : ℝ) + rhoV n a)


open Classical in
def topTypes (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  (((univ : Finset (Finset (Fin n × Fin n))).filter fun B => ∀ p ∈ B, p.1 < p.2).image fun B =>
    domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB B) - rhoV n).filter fun ν => StrictAnti (ν + rhoV n)

def LemmaHT : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam ∧
    ∀ ν ∈ topTypes lam, spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam)

def SecondTypeWeightsShorter : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν, IsSecondTypeWeight lam lev ν →
    ν ∈ topTypes lam ∧ nsq (ν + rhoV n) < nsq (muQ lam lev + rhoV n)

end PositivityTheory.RgBcC.RealD
end
end

section

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)

def LeviCommutantWordReduction : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), InvLv lev b →
    ∀ ν : Fin n → ℝ, (∀ a c, lev a = lev c → ν a = ν c) → ∃ z : FreeAlgebra ℂ (ℕ × ℂ),
      ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
        ∀ h : H, (∀ a c, lev a = lev c → (F1 a c + F2 a c) h = if a = c then (ν a : ℂ) • h else 0) →
          evLv lev F1 F2 b h = evCap lev F1 z h

def CapelliProductsScalar : Prop :=
  ∀ (n : ℕ) (L : Fin n → ℝ), StrictAnti L → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ν : Fin n → ℝ) (σ1 σ2 : ℕ → ℂ),
    (∀ j, (∑ a ∈ blk lev j, (ν a : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) = 2 * ∑ a ∈ blk lev j, (L a : ℂ)) →
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
    ∀ c : H, (∀ a b, lev a = lev b → (F1 a b + F2 a b) c = if a = b then (ν a : ℂ) • c else 0) →
      (∀ u : ℂ, capProd F1 lev σ1 u c = (∏ a, (u + (L a : ℂ))) • c) →
      (∀ u : ℂ, capProd F2 lev σ2 u c = (∏ a, (u + (L a : ℂ))) • c) →
      ∀ j u, capS F1 lev j u c = (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ))) • c

def InvPick : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam lev E1 E2 → ∀ (μ : Fin n → ℝ) (v w : V),
    v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → v ≠ 0 → (∃ x ∈ alg E1 E2, x v = w) → ∃ a, InvKP n a ∧ evKP E1 E2 a v = w

def LevStab : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → ∀ p q, lev p = lev q →
      ∀ x ∈ bdSub lev E1 E2, firstLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2 ∧ secondLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2

def LevRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → IsLevPairA lev (firstLeviFamily lev E1 E2) (secondLeviFamily lev E1 E2)

def SemiCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ a c, lev a = lev c →
        (firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c) (Pi.single (omU lev) v) =
          if a = c then ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ) • Pi.single (omU lev) v else 0

def CapCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∃ σ1 σ2 : ℕ → ℂ,
    (∀ j, (∑ a ∈ blk lev j, ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) =
      2 * ∑ a ∈ blk lev j, (Lr lam a : ℂ)) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ u : ℂ,
        capProd (firstLeviFamily lev E1 E2) lev σ1 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2 ∧
        capProd (secondLeviFamily lev E1 E2) lev σ2 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2

def MultiplicityAssembly : Prop :=
  InvPick → InjUU → HCdecLv → ActUU → LevStab → LevRel → SemiCls → CapCls → LeviCommutantWordReduction → CapelliProductsScalar → MultFor

end PositivityTheory.RgBcC.RealD
end
end
