module

import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqOf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

namespace RowTiePCEqSum

theorem subst_zero_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  apply _root_.GlobalTheory.RowLaw.EndBlock.subst_zero' <;> assumption

theorem hasSubst_unit {τ : Type} {T : MvPowerSeries τ C} (hT : MvPowerSeries.constantCoeff T = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit => T) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hT)

theorem subst_lin {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) {ι : Type}
    (s : Finset ι) (r : ι → C) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • MvPowerSeries.subst a (F i) := by

  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | exact map_smul _ _ _

theorem coeff_subst_tyS {τ : Type} [Finite τ] {l : ℕ} (hl : 2 ≤ l) {T : MvPowerSeries τ C}
    (hT : MvPowerSeries.constantCoeff T = 0) (a : ℕ → C) (μ : τ →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => T) (tyS l a)) =
      ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (T ^ (l ^ s)) := by
  intros
  apply _root_.GlobalTheory.RowLaw.GaugeDeriv.coeff_subst_tyS <;> assumption

section Add

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end Add

end RowTiePCEqSum


end Formalism.L2.FormalSeriesBounds
