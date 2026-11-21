import Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm
import Development.AutomorphicArithmetic.PrimitiveCosets.Imports
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

def FamCoreConstantBounds {eps : ℝ} (Fm : FamCore eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ i : Fm.Ix x, CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x

variable {Fam : ℝ → Type 1} {core : ∀ {eps : ℝ}, Fam eps → FamCore eps}
  {Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop}

theorem windowInequality_of_artinInputs
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (Λ : Level) : ChebyshevInequalityOnWindows @core @Tied Λ := by
  rintro eD eL eps he Fm ⟨C, xE, hE⟩ ⟨K, cHH, eK, CL, x0, hT⟩
  refine window_bound_of_pointwise_hosts (x0 := max x0 xE)
    (eD := eD) (eL := eL) (K := K) (cHH := cHH) (eK := eK) (C := C) he fun x hx hw => ?_
  obtain ⟨i, hi⟩ := h Fm eD eL K cHH eK CL x (hT x (le_of_max_le_left hx) hw)
  let host := ((core Fm).D x i).host
  exact ⟨_, host.toHostAx, host.TT, hE x (le_of_max_le_right hx) i, hi⟩

theorem zeroFreeOn_of_core {Q : PChar → Prop}
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (hW : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧ ChebyshevInequalityAtWindowScale @core @Tied la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_tiedWin fun ψ hψ => by
    obtain ⟨Λ, la, a, b, c⟩ := hW ψ hψ
    exact ⟨Λ, la, a, b, windowInequality_of_artinInputs h Λ, formB Λ, c⟩

end UpperTheory.Comparison₂

end
