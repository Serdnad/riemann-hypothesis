module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle001
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle001
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

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

structure IsFinAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : FinMaps F a a') (v : Pl F) : Prop where
  onto : (SB _).map (R.p v) = ⊤
  onto' : (SB _).map (R.p' v) = ⊤
  inv : augAt om v ≤ LinearMap.ker (R.p v)
  inv' : augAt om' v ≤ LinearMap.ker (R.p' v)
  equiv : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
    R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁'
  nontriv : Nontrivial (R.Pi v)
  irred : ∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤
  sph : v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0
  zeta : ∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩

def FinAt (Q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Chars F E → Pl F → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ v, Q F E X v →
      ∃ R, IsFinAt B G X om om' R v

def FinRam : Prop := FinAt fun _ _ _ _ _ _ _ X v => v ∈ X.T

def FinSplit : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ Nonempty (E →ₐ[F] Fv F v)

def FinInert : Prop := FinAt fun F E _ _ _ _ _ X v => v ∉ X.T ∧ IsEmpty (E →ₐ[F] Fv F v)

theorem kFin_of (h1 : FinRam) (h2 : FinSplit) (h3 : FinInert) : GlobalTheory.ThK.KFin := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  have h : ∀ v, ∃ R, IsFinAt B G X om om' R v := fun v => by
    by_cases hv : v ∈ X.T
    · exact h1 F E σ B a a' G X om om' hT v hv
    · rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | he
      · exact h3 F E σ B a a' G X om om' hT v ⟨hv, he⟩
      · exact h2 F E σ B a a' G X om om' hT v ⟨hv, he⟩
  choose R hR using h
  exact ⟨{ Pi := fun v => (R v).Pi v, p := fun v => (R v).p v, p' := fun v => (R v).p' v },
    fun v => (hR v).onto, fun v => (hR v).onto', fun v => (hR v).inv, fun v => (hR v).inv', fun v => (hR v).equiv,
    fun v => (hR v).nontriv, fun v => (hR v).irred, fun v => (hR v).sph, fun v hv => (hR v.1).zeta v.2 hv⟩

end PositivityTheory.ThK
end
end

section

noncomputable section

namespace PositivityTheory.ThK

open NumberField IsDedekindDomain GlobalTheory.AdelicU

theorem map_eq_of_ncard_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : HeightOneSpectrum (𝓞 F)) (h : (v.asIdeal.primesOver (𝓞 E)).ncard = 1) :
    ∃ w : HeightOneSpectrum (𝓞 E), Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := by
  classical
  haveI := v.isMaximal
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 h
  have hm : P ∈ v.asIdeal.primesOver (𝓞 E) := hP ▸ rfl
  haveI := hm.1
  haveI := hm.2
  have h0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  refine ⟨⟨P, hm.1, h0⟩, ?_⟩
  have e : P.ramificationIdx (𝓞 F) = 1 := P.ramificationIdx_eq_one (𝓞 F)
  have := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) v.ne_bot
  rw [this]
  simp [hP, e]

theorem inert_of_local : InertOf := by
  intro F E _ _ _ _ _ σ B hB v he
  haveI := hB.unram
  haveI := v.isMaximal
  have h1 := ncard_primesOver_le_two hB.cm v
  have h2 : (v.asIdeal.primesOver (𝓞 E)).ncard ≠ 2 := fun h =>
    not_nonempty_iff.2 he ((nonempty_split_iff hB.cm).2 h)
  have h3 : 0 < (v.asIdeal.primesOver (𝓞 E)).ncard := Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero _ _)
  exact map_eq_of_ncard_eq_one v (by omega)

end PositivityTheory.ThK
end
end

section

noncomputable section

namespace PositivityTheory.ThK.SplitDict

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def intInd {m n : ℕ} (v : Pl F) : Matrix (Fin m) (Fin n) (Fv F v) → ℂ :=
  Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1

def DictAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (v : Pl F)
    (τ : E →ₐ[F] Fv F v) : Prop :=
  ∃ (b : GL (Fin a) (Fv F v)) (b' : GL (Fin a') (Fv F v)) (c : GL (Fin (a + a')) (Fv F v))
    (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ))
    (ι' : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
    (gl : UA σ G.V.J → GL (Fin a) (Fv F v)) (gl' : UA σ G.V'.J → GL (Fin a') (Fv F v))
    (hl : UA σ G.W.J → GL (Fin (a + a')) (Fv F v)),
    G.M.IsLinW B.ψ τ b c ι ∧ G.M'.IsLinBar B.ψ τ b' c ι' ∧
    (∀ hv : v ∈ B.P, τ = B.τ ⟨v, hv⟩ → b = G.V.bas v ∧ b' = G.V'.bas v ∧ c = G.W.bas v) ∧
    ι (G.M.vac v) = intInd v ∧ ι' (G.M'.vac v) = intInd v ∧
    (∀ g ∈ UAt σ G.V (evFin F v), Reads v ι (om (g, 1)) (omA (chrW X.ν τ) (chrW X.β τ) (gl g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι (om (1, h)) (omA (chrW X.ν τ) (chrW X.β τ) 1 (hl h))) ∧
    (∀ g ∈ UAt σ G.V' (evFin F v), Reads v ι' (om' (g, 1)) (omB (chrW X.ν τ) (chrW X.α τ) (gl' g) 1)) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), Reads v ι' (om' (1, h)) (omB (chrW X.ν τ) (chrW X.α τ) 1 (hl h))) ∧
    (∀ x, ∃ h ∈ UAt σ G.W (evFin F v), hl h = x)

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v),
      DictAt B G X om om' v τ

def IndIwasawa : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (α β : kˣ →* ℂˣ), ∀ F ∈ indSp a a' α β, (∀ h ∈ GlobalTheory.SplitWeil.KO k (Fin (a + a')), F h = 0) → F = 0

def RamNonzero : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (a a' : ℕ) (ϖ : kˣ) (α β ν : kˣ →* ℂˣ), HidaSetting a a' ϖ α β ν → ¬ IsUnram ν →
    ∃ Φ ∈ GlobalTheory.SplitWeil.SB _, pRam a a' ϖ ν β Φ ≠ 0

end PositivityTheory.ThK.SplitDict
end
end
