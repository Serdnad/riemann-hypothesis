module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  apply _root_.GlobalTheory.CompanionTheory.LeibOrd.DerivTw.twAct_equiv <;> assumption

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((twist ρ χ).Equiv (twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    exact nonempty_twAct_equiv e _ _ _ (levi_stab ψ n)
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
