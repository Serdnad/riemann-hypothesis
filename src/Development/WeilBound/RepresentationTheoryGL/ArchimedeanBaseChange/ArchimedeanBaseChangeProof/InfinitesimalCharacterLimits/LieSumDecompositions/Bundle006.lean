module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle505
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle012
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle007
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
import Mathlib.RingTheory.Finiteness.Lattice
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
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle003

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem cap_coeff (a : ℕ) (τ : E →+* ℂ) (d : ℂ) : ∃ f : ℕ → Module.End ℂ (Sm E a), f a = 1 ∧ (∀ k, f k ∈ Zalg E a) ∧
    ∀ u : ℂ, cap τ (u + d) = ∑ k ∈ Finset.range (a + 1), u ^ k • f k := by
  obtain ⟨f, h1, hspan, heq⟩ := QdetCoeff.qdet_shift_coeff (Module.End ℂ (Sm E a)) a (Eop (a := a) τ) (d + ((a : ℂ) - 1) / 2)
  have hc : ∀ u : ℂ, cap τ (u + d) = Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) := fun u => by
    rw [← add_assoc]; rfl
  refine ⟨f, h1, fun k => ?_, fun u => (hc u).trans (heq u)⟩
  have hle : Submodule.span ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2))) ≤
      Subalgebra.toSubmodule (Zalg E a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, rfl⟩
    change Formalism.REAL.qdet (Eop (a := a) τ) (u + (d + ((a : ℂ) - 1) / 2)) ∈ Zalg E a
    rw [← hc u]
    exact cap_mem_Zalg τ _
  exact hle (hspan k)

def zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) : Submodule ℂ (Sm E a) :=
  Submodule.span ℂ (⋃ i, (fun z : Module.End ℂ (Sm E a) => z (b i)) '' (Zalg E a : Set (Module.End ℂ (Sm E a))))

theorem zspan_fd {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (hb : ∀ i, IsAutForm (b i)) : FiniteDimensional ℂ (zspan b) := by
  have : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (b i)) ''
      (Zalg E a : Set (Module.End ℂ (Sm E a))))) := fun i => (hb i).zfin
  rw [zspan, Submodule.span_iUnion]
  infer_instance

theorem zspan_le {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {L : Submodule ℂ (Sm E a)} (hb : ∀ i, b i ∈ L)
    (hL : ∀ z ∈ Zalg E a, ∀ φ ∈ L, z φ ∈ L) : zspan b ≤ L := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, z, hz, rfl⟩
  exact hL z hz _ (hb i)

theorem mem_zspan {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) (i : Fin k) : b i ∈ zspan b :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨i, 1, Subalgebra.one_mem _, rfl⟩)

theorem zspan_stable {a : ℕ} {k : ℕ} (b : Fin k → Sm E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∀ φ ∈ zspan b, z φ ∈ zspan b := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨i, rfl⟩, z', hz', rfl⟩ := hx
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, z * z', Subalgebra.mul_mem _ hz hz', rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open PositivityTheory.Rg.Rs.ParabolicProjection in
theorem node_holds : Node := by
  intro E _ _ _ r s _ _ U W₁ W₂ T hU hW₁ hW₂ hTe hmem hC₁ hC₂ φ₀ hφ₀U hφ₀
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hmem φ₀ hφ₀U).1
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀U).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw W₁ ((s : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  have hc₁ := hC₁ χ₁ hχ₁ hχ₁0
  obtain ⟨t₁, p₁, ht₁, hpos₁, hp₁e, hp₁V, hp₁0⟩ := hc₁
  have hf₁ : twMap r ((s : ℂ) / 2) p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r ((s : ℂ) / 2) p₁ (mulChi r (Model.absC E ((s : ℂ) / 2)) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r ((s : ℂ) / 2) p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw W₂ (-(r : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  have hc₂ := hC₂ χ₂ hχ₂ hχ₂0
  obtain ⟨t₂, p₂, ht₂, hpos₂, hp₂e, hp₂V, hp₂0⟩ := hc₂
  have hf₂ : twMap s (-(r : ℂ) / 2) p₂ (∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s (-(r : ℂ) / 2) p₂ (mulChi s (Model.absC E (-(r : ℂ) / 2)) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s (-(r : ℂ) / 2) p₂) hf₂

  have hI := indMap_holds E r s U (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) T (twMap r ((s : ℂ) / 2) p₁)
    (twMap s (-(r : ℂ) / 2) p₂) hU.1 hU.2 (isStable_tw hW₁.1 _) (isStable_tw hW₂.1 _) hTe hmem
    (twMap_equiv hW₁.1 hp₁e) (twMap_equiv hW₂.1 hp₂e)
  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI
  have hT'm : ∀ φ ∈ U, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) (T' φ) := by
    intro φ hφ
    refine ⟨hT'u φ hφ, fun k g => ?_⟩
    obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁' i)).1 m.1 *
        (twMap s (-(r : ℂ) / 2) p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  refine ⟨Tr.node t₁ t₂, T', ⟨ht₁, ht₂⟩, ⟨hpos₁, hpos₂⟩, hT'e, fun φ hφ => ?_, fun h => ?_⟩
  · rw [Tr.space]
    exact Submodule.subset_span ⟨hT'm φ hφ,
      InducedTensorMap.Main.finVec_of_equiv hT'e hφ (hU.2 φ hφ).kfin⟩
  · have e := hT's φ₀ hφ₀U k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end
