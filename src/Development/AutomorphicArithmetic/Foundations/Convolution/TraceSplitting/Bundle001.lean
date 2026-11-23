module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle157
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle001
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

theorem UpperTheory.ConvolutionTheory.T.goodEx :
    UpperTheory.ConvolutionTheory.T.GoodEx := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := k.isLt
    omega
  let ν : Fin (m + 1) → ℤ := fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)
  have hlast : ν (Fin.last m) = -S := by simp [ν]
  have hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ) := by
    intro k
    have : k.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last k).ne
    simp [ν, this]
  have hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ) := by
    intro i hi
    simp [ν, hi]
  have hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i := by
    intro i hi
    rw [hne i hi]
    have := i.isLt
    omega
  have hsum : ∑ i, ν i = 0 := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
    rw [← hS]
    ring
  have hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i := by
    intro J hJ hl
    refine Finset.sum_pos (fun i hi => hpos i ?_) hJ
    rintro rfl
    exact hl hi
  refine ⟨ν, ?_, hsum, ?_⟩
  · intro i j hij
    by_cases hj : j = Fin.last m
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        subst hj
        exact lt_irrefl _ hij
      have h1 := hpos i hi
      have h2 : ν j = -S := by rw [hj, hlast]
      show ν j < ν i
      omega
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        exact absurd (Fin.le_last j) (not_le.mpr hij)
      show ν j < ν i
      rw [hne i hi, hne j hj]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
  · intro J hJne hJu
    by_cases hl : Fin.last m ∈ J
    · have hc : Jᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hJu (by simpa using h)
      have h1 := hJ Jᶜ hc (by simpa using hl)
      have h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0 := by
        rw [Finset.sum_add_sum_compl, hsum]
      omega
    · exact (hJ J hJne hl).ne'
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

def AbsLast : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)]
    (m : Measure (Gw n v)) [m.IsHaarMeasure] (U : Subgroup (Gw n v)), CO U →
    ∀ (ι : Type) [Fintype ι] (τ : ι → SmIrr (Gw n v)) (a : ι → ℂ) (Z : ι → Multiset ℂ) (τ₀ : SmIrr (Gw n v)) (c : ℂ) (Z₀ : Multiset ℂ),
    c ≠ 0 → Z₀ ≠ 0 → 0 ∉ Z₀ → (∀ i, 0 ∉ Z i) → fixedVectors τ₀.ρ U ≠ ⊥ →
    (∀ (φ : Gw n v → ℂ) (s₀ : ℂ) (s : ι → ℂ), Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
      HasTrace m τ₀.ρ φ s₀ → (∀ i, HasTrace m (τ i).ρ φ (s i)) →
      ∀ᶠ j : ℕ in atTop, c * (Z₀.map (· ^ j)).sum * s₀ = ∑ i, a i * ((Z i).map (· ^ j)).sum * s i) →
    ∃ i, Nonempty ((τ i).ρ.Equiv τ₀.ρ)

def PullBack : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) →
    ∀ [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] [MeasurableSpace (Gw n w.1)] [BorelSpace (Gw n w.1)]
      (mF : Measure (Gw n v)) (mE : Measure (Gw n w.1)), mF.IsHaarMeasure → mE.IsHaarMeasure → ∀ τ' : SmIrr (Gw n w.1),
    ∃ (τ : SmIrr (Gw n v)) (r : ℂ), r ≠ 0 ∧ (∀ τ₁ : SmIrr (Gw n v), Nonempty (τ₁.ρ.Equiv τ.ρ) → LocIso w τ₁ τ') ∧
      (∀ (ψ : Gw n w.1 → ℂ) (s : ℂ), HasTrace mF τ.ρ (fun g => ψ (mapGL n (completionMap v w.1) g)) s → HasTrace mE τ'.ρ ψ (r * s)) ∧
      ∀ (J : Subgroup (Gw n w.1)) (U : Subgroup (Gw n v)), CO J → (∀ g, g ∈ U ↔ mapGL n (completionMap v w.1) g ∈ J) →
        CO U ∧ (fixedVectors τ'.ρ J ≠ ⊥ → fixedVectors τ.ρ U ≠ ⊥) ∧
        ∀ φ : Gw n v → ℂ, Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
          ∃ ψ : Gw n w.1 → ℂ, Test ψ ∧ (∀ u ∈ J, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) ∧
            φ = fun g => ψ (mapGL n (completionMap v w.1) g)

def UnitTrace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)), m.IsHaarMeasure →
    ∀ (τ : SmIrr (Gw n w)) (J : Subgroup (Gw n w)), Occurs μ V w τ → CO J → V ⊓ fixL μ w J ≠ ⊥ →
      fixedVectors τ.ρ J ≠ ⊥ ∧ Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) ∧
      (∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
        (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g) ∧
      ∃ s : ℂ, s ≠ 0 ∧ HasTrace m τ.ρ ((J : Set (Gw n w)).indicator 1) s

def OneTerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n l : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (V : Submodule ℂ (LL μ)) Λ t,
    IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V → At μ 𝔰.S V Λ t → ∀ (x : ℝ) (j : ℕ),
      𝔰.tr (fun V' => At μ 𝔰.S V' Λ t) x j = trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)

def SideSum : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (UF : ∀ v : Pl F, Subgroup (Gw n v)) (e : Fin n → ℤ),
      Antitone e → ∀ (p : Submodule ℂ (LL μ) → Prop) (x : ℝ), 0 < x →
      ∃ (ι : Type) (_ : Fintype ι) (V : ι → Submodule ℂ (LL μ)) (τ : ι → ∀ v : Pl F, SmIrr (Gw n v)) (b : ι → ℂ) (Z : ι → Multiset ℂ),
        (∀ i, IsSummand μ (V i) ∧ p (V i) ∧ 0 ∉ Z i ∧ ∀ v, Occurs μ (V i) v (τ i v)) ∧
        ∀ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S → (∀ v ∈ S, L.UF v = UF v) → GM.IsSideF L ν a e 𝔣 →
          ∀ s : ι → Pl F → ℂ, (∀ i, ∀ v ∈ S, HasTrace (m v) (τ i v).ρ (L.f v) (s i v)) → ∀ j : ℕ,
            𝔣.tr p x j = ∑ i, b i * ((Z i).map (· ^ j)).sum * ∏ v ∈ S, s i v

def PickS : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) Λ t, IsSummand μ V → AtAE μ V Λ t → ∀ v : Pl F,
      ∃ (S : Finset (Pl F)) (q : Pl F) (_ : PlacesOver E q), v ∈ S ∧ q ∉ S ∧ GM.Split E q ∧ (∀ u ∉ S, GM.Unr E u) ∧
        (∀ w : Pl E, w.under (𝓞 F) ∉ S → V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥) ∧
        ∀ S' : Set (Pl E), (∀ w, w ∈ S' ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q) →
          At μ S' V Λ t ∧ (∀ τ, (Λ τ).card = n) ∧ ∀ w ∉ S', (t w).card = n ∧ 0 ∉ t w

def PickInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL (K := E) (n := n))) [μE.IsHaarMeasure] (μF : Measure (normOneGL (K := F) (n := n))) [μF.IsHaarMeasure] (u : LL μE), u ≠ 0 →
      ∃ (m : ℕ) (_ : Module.finrank F E = m + 1) (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n)
        (hs : ∀ i, Continuous (s i)) (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (νF : Measure (archGroup F n))
        (_ : νF.IsHaarMeasure) (b a : TI F n) (aE : TI E n) (aF : TI F n), IsBlockElement D n s ∧ ArchSlot D νE νF b a aE aF ∧
        GM.AmpFn μE νE aE ∧ GM.AmpFn μF νF aF ∧ GM.ArchPair σ νE νF aE aF 1 ∧ OComponent μE (s 0) (hs 0) νF a u ≠ 0

def SplitLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, GM.Split E v →
      ∃ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)), CO U ∧
        U ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        ∀ u, CO (J u) ∧ (∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) ∧ V ⊓ fixL μ u.1 (J u) ≠ ⊥

def SplitStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      (∀ u g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
      (CO U → U ≤ GLnLocal.integralGL (v.adicCompletion F) n →
        ∃ UE : Subgroup (GL (Fin n) (CompletionsOver E v)), (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
          IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v)

def SplitMatch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (w : PlacesOver E v), GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      CO U → (∀ u, CO (J u) ∧ ∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      ∃ c : ℂ, ∀ ψ : Gw n w.1 → ℂ, Test ψ → (∀ u ∈ J w, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ))
          (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) g) ∧
        ∀ y ∈ U, ∀ g, ψ (mapGL n (completionMap v w.1) (y * g)) = ψ (mapGL n (completionMap v w.1) g)

def InertData : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, ¬ GM.Split E v →
      ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ) (f : Gw n v → ℂ)
        (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
        (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ RankOne μ V u.1 (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
        (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
        GM.MatchAt σ v 1 (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f ∧
        IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
        IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f (y * g) = f g

def OffStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), (U : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), ∀ g, g ∈ U ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      ∀ w : Pl E, CO (GLnLocal.integralGL (w.adicCompletion E) n) ∧ CO (GLnLocal.iwahori (w.adicCompletion E) n) ∧
        GLnLocal.iwahori (w.adicCompletion E) n ≤ GLnLocal.integralGL (w.adicCompletion E) n

end UpperTheory.ConvolutionTheory.T
end
end

section

noncomputable section

open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC UpperTheory.ConvolutionTheory.T

namespace UpperTheory.ConvolutionTheory.T.Ncs

private theorem loc_one_of {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem norm_surj {A B : Type} [Field A] [Field B] [Algebra A B] (hs : Function.Surjective (algebraMap A B))
    (x : Aˣ) : ∃ y : Bˣ, GroundTheory.LocalField.normUnits A B y = x := by
  have hfr : Module.finrank A B = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨(algebraMap A B).injective, hs⟩).finrank_eq
    simpa using this.symm
  refine ⟨Units.map (algebraMap A B).toMonoidHom x, Units.ext ?_⟩
  rw [GroundTheory.LocalField.coe_normUnits]
  change Algebra.norm A (algebraMap A B x) = x
  rw [Algebra.norm_algebraMap, hfr, pow_one]

private theorem loc_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (η : HChar F) (hη : IsNormChar E η) (v : HeightOneSpectrum (𝓞 F)) (hs : GM.Split E v)
    (x : (v.adicCompletion F)ˣ) : η.loc v x = 1 := by
  let ψ : HChar E := ⟨η.1.comp (GroundTheory.Global.ideleNorm F E), η.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg η.1 (GroundTheory.Global.ideleNorm_diagonal (K := F) k)).trans (η.2.2 _)⟩
  have hψ : ∀ x, ψ.1 x = η.1 (GroundTheory.Global.ideleNorm F E x) := fun _ => rfl
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ψ.val w = 1 := by
    filter_upwards [hη.2.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))] with w h1 h2
    have hf := GlobalTheory.ArtinTransport.normV_eq_pow (E := F) (E' := E) (v := w.under (𝓞 F)) (w := w) rfl
    obtain ⟨a, b⟩ := GlobalTheory.NormValGen.unrAt_val_of_comp_norm F E η ψ hψ w _ hf h2
    exact ⟨a, b.trans (h1 _ hf)⟩
  have h1 : ψ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ.1 ψ.2.1 ψ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of ψ w this.1 this.2 y
  obtain ⟨⟨w, hw⟩⟩ := GroundTheory.Global.nonempty_placesOver E v
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hw
  haveI := hw
  have hsurj := hs ⟨w, hw⟩
  obtain ⟨y, hn⟩ := norm_surj (A := (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (B := w.adicCompletion E) hsurj x
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 : η.1 (GroundTheory.Global.ideleNorm F E (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)) = 1 := by
    rw [← hψ, h1]; rfl
  rw [h2] at h3
  exact h3

private theorem twist_inter {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) (η : HChar F)
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ x, η.loc v x = 1) (g : GL (Fin n) (v.adicCompletion F)) (φ : π.V) :
    (π.twist η).locRep v g (π.toTwist η φ) = π.toTwist η (π.locRep v g φ) := by
  have hd : CuspSub.locDet n η v g = 1 := h _
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, ← CuspSub.locRep_eq]
  simp only [opAdd, zero_smul, add_zero]
  have e : opMul η (Op.fin (locGL F n v g)) = 1 := (CuspSub.chiDet_locGL η v g).trans hd
  rw [e, Units.val_one, one_smul]

end UpperTheory.ConvolutionTheory.T.Ncs

open UpperTheory.ConvolutionTheory.T.Ncs in
theorem UpperTheory.ConvolutionTheory.T.normCharSplit :
    UpperTheory.ConvolutionTheory.T.NormCharSplit := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ η hη v hs π τ
  have hl := loc_eq_one η hη v hs
  change (π.twist η).IsLocComp v τ ↔ π.IsLocComp v τ
  constructor
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).symm.toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).symm.injective ?_),
      fun g x => (π.toTwist η).injective ?_⟩
    · simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_zero] using LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← twist_inter π η v hl, LinearEquiv.apply_symm_apply, hf]
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).injective ?_),
      fun g x => ?_⟩
    · simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_zero] using LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [twist_inter π η v hl, hf]
end
end

section

theorem UpperTheory.ConvolutionTheory.T.matchOne :
    UpperTheory.ConvolutionTheory.T.MatchOne := by
  intro F E _ _ _ _ _ σ n v aE bE aF bF
  obtain ⟨⟨aE', bE', aF', bF', mE, mF, hE, hF, hE1, hF1⟩, h2⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
  obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
  exact ⟨mE, mF, hE, hF, hE1, hF1, fun c φ f hM => @h2 _ bE' _ bF' mE mF hE hF hE1 hF1 c φ f hM⟩
end
