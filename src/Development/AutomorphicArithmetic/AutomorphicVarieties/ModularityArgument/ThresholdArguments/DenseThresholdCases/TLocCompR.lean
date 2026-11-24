module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocCompROfAdmissibleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)
namespace UpperTheory.V.Af.RealLocalComponent
section Gen
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x
private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by

  simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]
private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]
private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this
private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c :=
  _root_.GlobalTheory.RealGal.LocCompRProof.exists_type κ φ hφ
end Gen
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]
private theorem fin_loc (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]
private theorem bot_or_top (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))
private theorem isotypic (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))
private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)
private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  apply _root_.UpperTheory.V.Af.Nf.LocalComponentIsotypic.exists_comp <;> assumption
end UpperTheory.V.Af.RealLocalComponent
theorem UpperTheory.V.Af.local_comp_real_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.LocCompR := fun P _ _ _ _ _ π w =>
  ⟨UpperTheory.V.Af.RealLocalComponent.exists_comp P.admR π w, UpperTheory.V.Af.RealLocalComponent.isotypic π w⟩
end
end
