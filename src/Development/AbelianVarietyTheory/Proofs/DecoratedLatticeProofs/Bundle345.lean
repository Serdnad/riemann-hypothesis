module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModL

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem ι_mul_incA (x : k) (b : D.host.E) : p.ι x * incA D b = p.ι (x * p.pr b) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι x * p.ι (p.π (incA D b))
  rw [p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, Witness.e_ι]

theorem map_ι_mul_rat {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map p.pr).map p.ι := by
  ext i j

  simp [Matrix.mul_apply, ι_mul_incA, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_iA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map p.pr = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have hβ : B.o.iA.map p.pr * FA.β = F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) := by
    ext r a
    rw [← h.1 r a]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  calc F₀.γ * B.o.iA.map p.pr = F₀.γ * (B.o.iA.map p.pr * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = fromRows FA.γ 0 := by
        rw [hβ, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices
end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem up_fromCols {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x (0 : Matrix n Unit k)) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have hX : FA.γ * B.o.qA.map p.pr = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) * F₀.γ := by
    rw [← core_qA p B FA F₀ h, Matrix.mul_assoc _ F₀.β, F₀.βγ, Matrix.mul_one]
  have hx : fromCols x (0 : Matrix n Unit k) = x * fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Place.up, Place.up, OrthDec.pA, rat, map_ι_mul_rat, Matrix.mul_assoc (FS.β * x), hX, hx]
  simp only [Matrix.mul_assoc]

theorem up_jA {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀)
    (t : Matrix n (n' ⊕ Unit) k) : p.up F₀ FS t ⬝ B.o.jA = p.up FA FS t.toCols₁ := by
  rw [Place.up, Place.up, OrthDec.jA, rat, map_ι_mul_rat, Matrix.mul_assoc _ F₀.γ, core_iA p B FA F₀ h]
  conv_lhs => rw [← fromCols_toCols t]
  rw [Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO V S → ℂ) (a u : WO A S) (z : WO L S) :
    heisO ψ V S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, z)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, z)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ (T₁ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ S → ℂ)), p.IsModel ψ F₀ FS T₁ → ∀ (φ₀ : SB (n → k)) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ (v : WO S B'.A) (T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ)), (∀ Ξ₁ u, T Ξ₁ u = GlobalTheory.Unf.contr l S vL (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁)) Ξ₂ u v) → p.IsModel ψ FA FS T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n' _ _ _ _ FA F₀ FS hcore T₁ hT₁ φ₀ Ξ₂ hΞ₂ v T hT

  have pass : ∀ (a : WO B.A S) (Φ Φ' : SB (Matrix n n' k)),
      T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ') =
        heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) →
      T Φ' = heisO ψ B.A S a (T Φ) := by
    intro a Φ Φ' e
    funext u
    rw [hT Φ' u, e]
    change _ = ψ (symplOH B.A S u a) * T Φ (u + a)
    rw [hT Φ (u + a)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ hΞ₂
    have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) :=
      hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))
    have hint : Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₂).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₂ _)
    have h := GlobalTheory.SuperposS.superpos_isTheta D ψ hψ B.V₀ B.A B.L S B.o (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ))
      (hT₁.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) (l.κ S) (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)))
      (GlobalTheory.ContractionLocal.continuous_kappa l S).measurable hint
    convert h using 1
    funext u
    rw [hT]
    rfl
  ·
    refine pass (p.up FA FS x) Φ Φ' ?_
    rw [← up_fromCols p B S FA F₀ FS hcore x]
    refine hT₁.trans _ _ _ fun t => ?_
    have h1 : (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x := by
      ext i j; simp [Matrix.toCols₁]
    have h2 : (fun r => (t + fromCols x (0 : Matrix n Unit k)) r (Sum.inr ())) = fun r => t r (Sum.inr ()) := by
      funext r; simp
    simp only [GlobalTheory.ContractionLocal.colTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₁.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [← mul_assoc, hy i c]
    · simp only [GlobalTheory.ContractionLocal.colTens_apply, e]
      rw [B.o.symplO_resS S (p.up F₀ FS t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resS_apply B.o S (p.up F₀ FS t)]
      simp only
      rw [up_jA p B S FA F₀ FS hcore t]
      have : symplO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by
        have h0 : hO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModL

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∃ ψk : AddChar k Circle, p.IsChar ψ ψk) ∧ (∀ ψk : AddChar k Circle, p.IsChar ψ ψk → Continuous ψk ∧ ψk ≠ 1) ∧ p.xi ≠ 0 ∧ (∀ x y, p.ι (x * y) = p.ι x * p.ι y) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  first | exact @GlobalTheory.LocChar.weil_char_split | exact GlobalTheory.LocChar.weil_char_split | (intros; apply GlobalTheory.LocChar.weil_char_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ModSB

theorem continuous_pi_hO_up {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : (fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y)) = fun t =>
      ∑ a, ∑ b, ∑ c, ∑ d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D (y c b)) * p.π (incA D (T.gram c d)) *
        (FT.β * t * FS.γ) d a := by
    funext t
    unfold hO

    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    simp only [GlobalTheory.LocMod.Place.up, Matrix.map_apply, p.π_ι]
  rw [h]
  have hm : Continuous fun t : Matrix Y Y' k => FT.β * t * FS.γ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ =>
    continuous_finsetSum _ fun d _ => continuous_const.mul (hm.matrix_elem d a)

theorem mul_char_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (y : WO S T), IsHalf (cA D p.e) y → ∀ Φ ∈ SB (Matrix Y Y' k), (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) ∈ SB (Matrix Y Y' k) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT y hy Φ hΦ
  obtain ⟨⟨ψk, hk⟩, hc, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  have hcont := (hc ψk hk).1
  have heq : (fun t => ψ (symplO S T (p.up FS FT t) y) * Φ t) =
      fun t => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ) * Φ t := by
    funext t
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hk t y]
  rw [heq]
  have hl : IsLocallyConstant (fun t : Matrix Y Y' k => ((ψk (p.π (hO S T (p.up FS FT t) y)) : Circle) : ℂ)) :=
    ((GlobalTheory.IrredSB.char_isLocallyConstant ψk hcont).comp_continuous (continuous_pi_hO_up p FS FT y)).comp
      (fun z : Circle => (z : ℂ))
  exact ⟨hl.mul hΦ.1, HasCompactSupport.mul_left hΦ.2⟩

end GlobalTheory.ModSB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

theorem _root_.GlobalTheory.T.exists_schwartzBruhat_extByZero_of_splitPlaceHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  first | exact @GlobalTheory.SBOfHalf.exists_sb_ext_eq | exact GlobalTheory.SBOfHalf.exists_sb_ext_eq | (intros; apply GlobalTheory.SBOfHalf.exists_sb_ext_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitLocalPlace_local_models_linear_subspace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  first | exact @GlobalTheory.LocMod.Place.isModel_linear | exact GlobalTheory.LocMod.Place.isModel_linear | (intros; apply GlobalTheory.LocMod.Place.isModel_linear <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_local_model_slice_target_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  first | exact @GlobalTheory.SliceModelT.main | exact GlobalTheory.SliceModelT.main | (intros; apply GlobalTheory.SliceModelT.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_local_model_slice_source_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  first | exact @GlobalTheory.SliceModel.exists_isModel_slice | exact GlobalTheory.SliceModel.exists_isModel_slice | (intros; apply GlobalTheory.SliceModel.exists_isModel_slice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_model_box_product_orthogonal_sum_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S X T L'' : HSp D) (o'' : OrthDec X T L'') (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank n) (FT : Frame k T.rank Z) (FL : Frame k L''.rank Unit) (FX : Frame k X.rank (Z ⊕ Unit)), FX.β = fromCols (o''.iA.map p.pr * FT.β) (o''.iB.map p.pr * FL.β) → ∀ T₂ TL, p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FL TL → ∀ TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ), (∀ (a : SB (Matrix Z n k)) (b : SB (Matrix Unit n k)) (Φ : SB (Matrix (Z ⊕ Unit) n k)), (∀ x, Φ.1 x = a.1 x.toRows₁ * b.1 x.toRows₂) → TX Φ = o''.boxT S (T₂ a) (TL b)) → p.IsModel ψ FS FX TX := by
  first | exact @GlobalTheory.LocMod.BoxModel.isModel_boxT | exact GlobalTheory.LocMod.BoxModel.isModel_boxT | (intros; apply GlobalTheory.LocMod.BoxModel.isModel_boxT <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_model_restricted_to_line_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  first | exact @GlobalTheory.SliceLine.slice_line | exact GlobalTheory.SliceLine.slice_line | (intros; apply GlobalTheory.SliceLine.slice_line <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrp
open GlobalTheory.LocMod GlobalTheory.RootEx GlobalTheory.SplitWeil

theorem isLoc_embA : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ (h : GA D B.A) (γ : GL n k), p.IsLoc FA h γ → p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c γ) := by
  intro D k _ _ _ _ p n _ _ c ρ B s FA F hF h γ hh
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  rw [embA_apply]
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ γ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.LocGrp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) , (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), (∀ gk : GL Y k, ∃! g, p.IsLoc F g gk) ∧ (∀ g, SuppAt p.e S g → ∃ gk, p.IsLoc F g gk) ∧ ∀ g gk h hk, p.IsLoc F g gk → p.IsLoc F h hk → p.IsLoc F (g * h) (gk * hk)) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ g β q, q ∈ R k n c (ρ + 1) → p.IsLoc F g (colE c (ρ + 1) β * q) → g ∈ jacGrp J.d) ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ g q, q ∈ R k n c (ρ + 1) → p.IsLoc F g q → g ∈ besGrp B.d B.o := by
  first | exact @GlobalTheory.LocGrp.local_groups | exact GlobalTheory.LocGrp.local_groups | (intros; apply GlobalTheory.LocGrp.local_groups <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  first | exact @GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | exact GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | (intros; apply GlobalTheory.LocMod.OutsideOrth.mul_eq_zero <;> assumption)
end
