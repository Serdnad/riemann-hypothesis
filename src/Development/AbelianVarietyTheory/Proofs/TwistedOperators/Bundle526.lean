module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle501
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle505
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeAdm

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def smAut (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f}
  add_mem' := fun ha hb => GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb
  zero_mem' := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V
  smul_mem' := fun c _ ha => GlobalTheory.Mem.AutSpace.isAutFunSm_smul c ha

theorem isAutFunSm_of_mem_gkGen (hθ : IsInfFam θ) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, IsAutFunSm θ V f := by
  have hA : GlobalTheory.CuspGK.IsGKSub θ M (smAut θ V) :=
    ⟨fun τ g hg f hf => GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf τ g hg.1,
      fun τ X hX f hf => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf⟩
  exact fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := smAut θ V) hψ hA hf

theorem level_gkGen {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g := by
  obtain ⟨U, hU, hψU⟩ := hψ.level
  let A : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g}
      add_mem' := fun ha hb u hu hu' g => by simp only [Pi.add_apply, ha u hu hu' g, hb u hu hu' g]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c f hf u hu hu' g => by simp only [Pi.smul_apply, hf u hu hu' g] }
  have hA : GlobalTheory.CuspGK.IsGKSub θ M A := by
    refine ⟨fun τ g _ f hf u hu hu' x => ?_, fun τ X _ f hf u hu hu' x => ?_⟩
    · show f (x * u * atTau θ V τ g) = f (x * atTau θ V τ g)
      rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) hu',
        ← mul_assoc]
      exact hf u hu hu' _
    · have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hu' τ X f) x
      rw [show rTr V u f = f from funext (hf u hu hu')] at this
      exact this.symm
  exact ⟨U, hU, fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := A) (fun u hu hu' g => hψU u hu hu' g) hA hf⟩

theorem gelf_mem_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (τ : D.what₂.Tau) (k : ℕ) :
    ∀ f ∈ A, gelf θ V τ k f ∈ A := by
  intro f hf
  have hC : ∀ Z, ∀ g ∈ A, RderC θ V τ Z g ∈ A := fun Z g hg => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact A.add_mem (hA.lie τ _ h1 g hg) (A.smul_mem _ (hA.lie τ _ h2 g hg))
  have key : ∀ l : List ((GA D V → ℂ) → (GA D V → ℂ)), (∀ F ∈ l, ∀ g ∈ A, F g ∈ A) →
      l.foldr (fun F acc => F acc) f ∈ A := by
    intro l hl
    induction l with
    | nil => exact hf
    | cons F l ih => exact hl F (by simp) _ (ih fun F' hF' => hl F' (by simp [hF']))
  refine Submodule.sum_mem _ fun idx _ => key _ fun F hF => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hF
  exact hC _

end GlobalTheory.KTypeAdm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspApprox

open MeasureTheory Matrix Formalism.REAL GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem avgN_weighted_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau)
    (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) →
        ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  intro D θ hθ N τ e he a
  set P := N.M.fr τ with hPdef
  have hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun k =>
    GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P :=
    (continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const
  have hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ N.V τ).comp_continuous hκ hU
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn
  have hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H| := fun k => by
    have h := hH k (Set.mem_univ k)
    simp only [Function.comp_apply, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hne : Continuous fun k => ‖e k‖ := he.norm
  refine ⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩
  have hq := quotHeight_pos N.V g
  have hqa : 0 < quotHeight N.V g ^ a := pow_pos hq a
  have hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤
      ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) := by
    intro k
    set A := atTau θ N.V τ (P⁻¹ * toMK k * P)
    have h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H| := by
      have h := quotHeight_mul_le N.V (g * A) A⁻¹
      rw [mul_inv_cancel_right, height_inv] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)
    have h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hq.le h1 a
    have h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a :=
      calc ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ ‖f (g * A)‖ * (quotHeight N.V (g * A) ^ a * |H| ^ a) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (‖f (g * A)‖ * quotHeight N.V (g * A) ^ a) * |H| ^ a := by ring
        _ ≤ B * |H| ^ a := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_div_iff₀ hqa]; exact h3
  have hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤
      ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ)) :=
    norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const))
      (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const] at hint
  calc ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * quotHeight N.V g ^ a
      ≤ ((∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * (B * |H| ^ a / quotHeight N.V g ^ a)) * quotHeight N.V g ^ a :=
        mul_le_mul_of_nonneg_right hint hqa.le
    _ = (∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a * B := by field_simp

end GlobalTheory.KFinCuspApprox

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (restrictPol P p) (restrictPol P q), polOf P a)
    rw [restrictPol_comp P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} (d : p.Fam S)
    (d' : p.Fam S') : ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
    Path.Fam.zip φ (d.append e) (d'.append e') = (Path.Fam.zip φ d d').append (Path.Fam.zip φ e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
    show (Path.Fam.zip φ (d.append e.1) (d'.append e'.1), φ a e.2 e'.2) =
      ((Path.Fam.zip φ d d').append (Path.Fam.zip φ e.1 e'.1), φ a e.2 e'.2)
    rw [zip_append φ d d' q e.1 e'.1]

theorem zip_rowFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ n (f : ∀ i : Fin n, S (.right i j))
    (g : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip φ (rowFam j n f) (rowFam j n g) = rowFam j n fun i => φ _ (f i) (g i)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (Path.Fam.zip φ (rowFam j n fun i => f i.castSucc) (rowFam j n fun i => g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n))) =
      (rowFam j n fun i => φ _ (f i.castSucc) (g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n)))
    rw [zip_rowFam φ j n]

theorem zip_downFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ n (f : ∀ j : Fin n, S (.down t i j))
    (g : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip φ (downFam t i n f) (downFam t i n g) = downFam t i n fun j => φ _ (f j) (g j)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show Path.Fam.zip φ (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), g (Fin.last n)) (downFam t i n fun j => g j.castSucc)) =
      Path.Fam.append (p := Path.one (.down t i n)) ((), φ _ (f (Fin.last n)) (g (Fin.last n)))
        (downFam t i n fun j => φ _ (f j.castSucc) (g j.castSucc))
    refine (zip_append φ (p := Path.one (.down t i n)) (((), f (Fin.last n)) : (Path.one (.down t i n)).Fam S)
      (((), g (Fin.last n)) : (Path.one (.down t i n)).Fam S') (downPath t i n) (downFam t i n fun j => f j.castSucc)
      (downFam t i n fun j => g j.castSucc)).trans ?_
    rw [zip_downFam φ t i n]
    rfl

theorem restrictPol_rowPath (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) = rowFam j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
    show (restrictPol P (rowPath T j n), polOf P (.right n j)) = (rowFam j n fun i => polOf P (.right (i.castSucc : Fin (n + 1)) j), _)
    rw [restrictPol_rowPath P j n]
    rfl

theorem restrictPol_downPath (P : PolE G) (t : T) (i : ℕ) : ∀ n,
    restrictPol P (downPath t i n) = downFam t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
    show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
    rw [restrictPol_comp, restrictPol_downPath P t i n]
    rfl

theorem tensE_single (W : G.Weil) {X Y : Node} (p : Path T X Y) (P : PolE G) (d : PureT G p) (c : ℂ) :
    tensE W p (Finsupp.single P 1) (Finsupp.single d c) =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) c := by
  unfold tensE tensT
  rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul]
  · simp
  · simp

theorem zip_given (W : G.Weil) (t : T) (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank)
    (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) :
    Path.Fam.zip (fun a (g : Sch G a) Q => W.fock a.pair g Q) (givenFin W t f Φ) (restrictPol (gPol ρ q) (givenPath t D.R.m)) =
      Path.Fam.append (colPure W t f fun j => q j) (rowDatum W ρ Φ) := by
  unfold givenFin givenPath
  rw [restrictPol_comp, zip_append, restrictPol_downPath, restrictPol_rowPath, zip_downFam, zip_rowFam]
  congr 1
  unfold rowDatum
  congr 1
  funext i
  show W.fock (.chi i 0) (W.cosVec i (Φ i)) (if h : (i : ℕ) < D.R.m then ρ ⟨i, h⟩ else 0) = W.datum ρ Φ i
  rw [dite_eq_left i.2]
  rfl

end GlobalTheory.FlipStart


end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}


open Classical in
def givenFn (B : Frames G) (t : T) (Φ : G.Datum) (e : AE D) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) : ℂ :=
  if IsHalf e x then ∏ w ∈ locPl G t, givenDatum t w B Φ (edgeOf a) (locArg B t w a x) else 0

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tensor_given (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (y : ∀ j : Fin D.R.m, WO (G.pS (Arrow.down t 0 j).pair) (G.pT (Arrow.down t 0 j).pair))
    (x : ∀ i : Fin D.R.m, WO (G.pS (Arrow.right (T := T) i 0).pair) (G.pT (Arrow.right (T := T) i 0).pair)) :
    (givenStage t w B Φ).tensor (pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x))) =
      (∏ j : Fin D.R.m, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) (y j))) *
        ∏ i : Fin D.R.m, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) (x i)) := by
  have pathArgs_down (i : ℕ) : ∀ (n : ℕ) (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair))
      (j : ℕ) (h : j < n), pathArgs B t w (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) (.theta i j) =
        locArg B t w (.down t i j) (y ⟨j, h⟩) := by
    intro n
    induction n with
    | zero => intro y j h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro y j h
      have hc := GlobalTheory.OppConv.pathArgs_comp B t w (Path.one (.down t i n)) ((), y (Fin.last n)) (.theta i j) (downPath t i n)
        (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)
      by_cases hj : j < n
      · exact (hc.1 ((GlobalTheory.OppConv.mem_edges_down t i n _).2 ⟨j, hj, rfl⟩)).trans (ih _ j hj)
      · have hj' : j = n := by omega
        subst hj'
        refine (hc.2 fun h' => ?_).trans ?_
        · obtain ⟨k, hk, hk'⟩ := (GlobalTheory.OppConv.mem_edges_down t i j _).1 h'
          simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
          omega
        · exact dif_pos rfl
  have hθ : ∀ j : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.theta 0 j) = locArg B t w (.down t 0 j) (y j) := by
    intro j
    refine ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.theta 0 j) (rowPath T 0 D.R.m) _).2 ?_).trans
      (pathArgs_down 0 D.R.m y j j.2)
    rw [GlobalTheory.OppConv.mem_edges_row]
    rintro ⟨i, -, h⟩
    cases h
  have hex : ∀ i : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.ex i 0) = locArg B t w (.right i 0) (x i) :=
    fun i => ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.ex i 0) (rowPath T 0 D.R.m) _).1
      ((GlobalTheory.OppConv.mem_edges_row 0 D.R.m _).2 ⟨i, i.2, rfl⟩)).trans (GlobalTheory.OppConv.pathArgs_row B t w 0 D.R.m x i i.2)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b _).prod = _
  simp only [GlobalTheory.SplitFlip.givenPath, List.map_append, List.prod_append, List.map_map, List.map_reverse, List.prod_reverse]
  have hl : ∀ f : ℕ → ℂ, ((List.range D.R.m).map f).prod = ∏ i : Fin D.R.m, f i := fun f => by
    rw [← Finset.prod_range, Finset.prod_eq_multiset_prod]; rfl
  rw [hl, hl]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [hθ j]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [hex i]
    rfl

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem repFin_of (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (Φ : G.Datum) (e : AE D) (he : IsIdemSum e (locPl G t)) (c : Fin D.R.m → ℂ) (z : ℂ) (hz : z * ∏ j, c j = 1)
    (hcol : ∀ j : Fin D.R.m, IsLocVec W (.mu t 0 j) e (ρ.vT 0 j) (c j • givenFn B t Φ e (.down t 0 j)) (f j))
    (hrow : ∀ i : Fin D.R.m, IsLocVec W (.chi i 0) e (ρ.vX i 0) (givenFn B t Φ e (.right i 0)) (W.cosVec i (Φ i))) :
    RepFin B ρ t (givenPath t D.R.m) (Finsupp.single (givenFin W t f Φ) z) (fun w => (givenStage t w B Φ).tensor) := by
  have append_surj {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
      ∀ {Z : Node} (q : Path T Y Z) (f : (p.comp q).Fam S), ∃ d e, Path.Fam.append (q := q) d e = f := by
    intro Z q
    induction q with
    | nil => intro f; exact ⟨f, (), rfl⟩
    | snoc a q ih =>
      intro f
      obtain ⟨d, e, h⟩ := ih f.1
      refine ⟨d, (e, f.2), ?_⟩
      show (Path.Fam.append (q := q) d e, f.2) = f
      rw [h]
      rfl
  have rowFam_surj {S : Arrow T → Type} (j : ℕ) : ∀ n (d : (rowPath T j n).Fam S), ∃ f, rowFam j n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun i => i.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨f, hf⟩ := ih d.1
      refine ⟨Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f, ?_⟩
      show (rowFam j n (fun i => Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f i.castSucc),
        Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f (Fin.last n)) = d
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  have downFam_surj {S : Arrow T → Type} (i : ℕ) : ∀ n (d : (downPath t i n).Fam S), ∃ f, downFam t i n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun j => j.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨d0, e, he⟩ := append_surj (Path.one (.down t i n)) (downPath t i n) d
      obtain ⟨f, hf⟩ := ih e
      refine ⟨Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f, ?_⟩
      rw [← he]
      show Path.Fam.append (p := Path.one (.down t i n)) ((), Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f (Fin.last n))
        (downFam t i n fun j => Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f j.castSucc) = _
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  refine ⟨e, he, fun _ => Path.Fam.append (q := rowPath T 0 D.R.m)
    (downFam t 0 D.R.m fun j => c j • givenFn B t Φ e (.down t 0 j)) (rowFam 0 D.R.m fun i => givenFn B t Φ e (.right i 0)),
    fun d hd => ?_, fun x hx => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ (by rintro rfl; simp at hz), Finset.mem_singleton] at hd
    subst hd
    exact (GlobalTheory.OppConv.vecAll_append ρ e _ _ _ _ _ _).2
      ⟨(GlobalTheory.OppConv.vecAll_down ρ e t 0 _ _ _).2 hcol, (GlobalTheory.OppConv.vecAll_row ρ e 0 _ _ _).2 hrow⟩
  · rw [Finsupp.sum_single_index (by rw [zero_mul])]
    obtain ⟨x₁, x₂, rfl⟩ := append_surj (downPath t 0 D.R.m) (rowPath T 0 D.R.m) x
    obtain ⟨y, rfl⟩ := downFam_surj 0 D.R.m x₁
    obtain ⟨y', rfl⟩ := rowFam_surj 0 D.R.m x₂
    obtain ⟨h1, h2⟩ := (GlobalTheory.OppConv.halfAll_append e _ _ _ _).1 hx
    have hy := (GlobalTheory.OppConv.halfAll_down e t 0 _ _).1 h1
    have hy' := (GlobalTheory.OppConv.halfAll_row e 0 _ _).1 h2
    dsimp only
    rw [Finset.prod_congr rfl fun w _ => tensor_given B t Φ w y y']
    erw [GlobalTheory.OppConv.famProd_append (downPath t 0 D.R.m), GlobalTheory.OppConv.famProd_down, GlobalTheory.OppConv.famProd_row]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, givenFn, if_pos (hy _), if_pos (hy' _)]
    rw [Finset.prod_comm (s := Finset.univ) (t := locPl G t), Finset.prod_comm (s := Finset.univ) (t := locPl G t),
      ← mul_assoc, ← mul_assoc, hz, one_mul]

end GlobalTheory.FlipStart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : GlobalTheory.MovedKappaEx.UnitAt q a)
    (hub : GlobalTheory.MovedKappaEx.UnitAt q b) : GlobalTheory.MovedKappaEx.UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dite_eq_left hab, dite_eq_left ha', dite_eq_left hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

end GlobalTheory.RatMoveJets
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  first | exact @GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | exact GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF | (intros; apply GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF <;> assumption)
end
