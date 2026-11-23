module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKUnif

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def Good (θ : InfFam D) (V : HSp D) (U : Subgroup (GA D V)) (N : ℕ) (φ : GA D V → ℂ) : Prop :=
  (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤

variable {θ : InfFam D} {U : Subgroup (GA D V)} {N : ℕ} {φ ψ : GA D V → ℂ}

theorem good_add (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) (hs' : ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (h : Good θ V U N φ) (h' : Good θ V U N ψ) : Good θ V U N (φ + ψ) :=
  ⟨fun k hk hk' g => by simp only [Pi.add_apply, h.1 k hk hk' g, h'.1 k hk hk' g],
    fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2 d, h'.2 d⟩) (GlobalTheory.Size.growthSob_add_le hs hs' d N)⟩

theorem good_smul (c : ℂ) (h : Good θ V U N φ) : Good θ V U N (c • φ) :=
  ⟨fun k hk hk' g => by simp only [Pi.smul_apply, h.1 k hk hk' g],
    fun d => by rw [GlobalTheory.Size.growthSob_smul]; exact ENNReal.mul_ne_top enorm_ne_top (h.2 d)⟩

theorem good_zero : Good θ V U N 0 := by
  have h := good_smul (θ := θ) (U := U) (N := N) (φ := 0) 0
  rw [zero_smul] at h
  refine h ⟨fun _ _ _ _ => rfl, fun d => ?_⟩
  have e := GlobalTheory.Size.growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N
  rw [zero_smul, enorm_zero, zero_mul] at e
  rw [e]; exact ENNReal.zero_ne_top

theorem good_Rder (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (h : Good θ V U N φ) :
    Good θ V U N (Rder θ V τ X φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · have e : rTr V k φ = φ := funext (h.1 k hk hk')
    have := congrFun (GlobalTheory.Size.Rder_rTr_fin (θ := θ) hk' τ X φ) g
    rw [e] at this
    exact this.symm
  · rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
    have hB : ∀ a b, ‖X a b‖ₑ ≤ ∑ a', ∑ b', ‖X a' b'‖ₑ := fun a b =>
      (Finset.single_le_sum (f := fun b' => ‖X a b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ a))
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.Size.Translate.growthSob_RderC_le hθ hs τ hB d N)
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ (h.2 (d + 1)))
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top

theorem good_rTr (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {h : GA D V} (hh : h ∈ GinfC V)
    (hg : Good θ V U N φ) : Good θ V U N (rTr V h φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · show φ (g * k * h) = φ (g * h)
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V hh hk', ← mul_assoc, hg.1 k hk hk']
  · obtain ⟨C, m, hC⟩ := GlobalTheory.Size.Translate.growthSob_rTr_le D θ hθ V d N
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hg.2 d)) (hC h hh φ hs)

theorem conj_mem_lieSet (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : M.fr τ * X * (M.fr τ)⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ) := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  rw [← M.fr_gram τ] at hX'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0
  have e : (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) =
      ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
        (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * X) * (M.fr τ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem dRep_mem_kFin (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {w : M.H τ}
    (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : dRep (M.rep τ) X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hd : dRep (M.rep τ) X w = dRep (M.σ τ) (M.fr τ * X * (M.fr τ)⁻¹) w := by
    unfold dRep
    congr 1
    funext t
    show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) w = _
    rw [← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
  rw [hd]
  exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ _ hstd w hw _ (conj_mem_lieSet M τ hX)

end GlobalTheory.GKUnif

namespace GlobalTheory.GKUnif

theorem exists_level_exponent : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧
      ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  intro hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
  have hne : ∀ τ, ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  choose u₀ hu₀ using hne
  obtain ⟨U, hU, hUl⟩ := (hT₀.1 u₀).level
  obtain ⟨N, hN⟩ := GlobalTheory.Size.exists_growthSob_ne_top (hT₀.2.1 u₀) (hT₀.2.2.2.2.1 u₀)
  have hsm : ∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hT₀.2.1
  suffices key : ∀ s : Finset D.what₂.Tau, ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (∀ τ ∉ s, u τ = u₀ τ) →
      Good θ V U N (T₀ u) from
    ⟨U, N, hU, fun u => key Finset.univ u (fun τ h => absurd (Finset.mem_univ τ) h)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    have : u = u₀ := funext fun τ => hu τ (Finset.notMem_empty τ)
    subst this
    exact ⟨hUl, hN⟩
  | insert τ s hτ ih =>
    intro u hu
    let Wk : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :=
      { carrier := {w | Good θ V U N (T₀ (Function.update u τ w))}
        add_mem' := fun {a b} ha hb => by
          show Good θ V U N (T₀ (Function.update u τ (a + b)))
          rw [T₀.map_update_add]
          exact good_add (hsm _) (hsm _) ha hb
        zero_mem' := by
          show Good θ V U N (T₀ (Function.update u τ 0))
          rw [T₀.map_update_zero]
          exact good_zero
        smul_mem' := fun c a ha => by
          show Good θ V U N (T₀ (Function.update u τ (c • a)))
          rw [T₀.map_update_smul]
          exact good_smul c ha }
    let W : Submodule ℂ (M.H τ) := Wk.map (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
    have hmemW : ∀ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk → (y : M.H τ) ∈ W := fun y hy => ⟨y, hy, rfl⟩
    have hWk : ∀ w ∈ W, ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk ∧ (y : M.H τ) = w := by
      rintro w ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    have hle : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := Submodule.map_subtype_le _ _
    have hlie : ∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W := by
      intro X hX w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨dRep (M.rep τ) X y, dRep_mem_kFin hHC M τ hX y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.2 τ X hX (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_Rder hθ (hsm _) hX hy
    have hK : ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W := by
      intro k hk w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨M.rep τ k y, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.rep_mem_kFin M τ hk y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.1 τ k hk (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_rTr hθ (hsm _) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ k) hy
    have h0 : u₀ τ ∈ Wk := by
      show Good θ V U N (T₀ (Function.update u τ (u₀ τ)))
      refine ih _ fun τ' h' => ?_
      by_cases e : τ' = τ
      · subst e; simp
      · rw [Function.update_of_ne e]
        exact hu τ' (by simp [e, h'])
    have hWne : W ≠ ⊥ := fun hb => hu₀ τ (Subtype.ext (by
      have := hmemW _ h0
      rw [hb] at this
      simpa using this))
    have hall := GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel hHC D V S M τ W hle hlie hK hWne
    obtain ⟨y, hy, hyu⟩ := hWk _ (hall (u τ).2)
    have : y = u τ := Subtype.ext hyu
    subst this
    have e : Function.update u τ (u τ) = u := Function.update_eq_self τ u
    have hy' : Good θ V U N (T₀ (Function.update u τ (u τ))) := hy
    rwa [e] at hy'

end GlobalTheory.GKUnif

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.HalfModTorus

open GlobalTheory.Doubling

theorem compFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AE D) (h : finPart D y = 1) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v y = 1 := by
  have h' : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y = 1 := h
  have e : GlobalTheory.AdelicU.compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e, h', map_one]

theorem unitFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : (AE D)ˣ) (h : finPart D (x : AE D) = 1) :
    unitFin D.host.F D.host.E v x = 1 :=
  Units.ext (compFin_eq_one v (x : AE D) h)

theorem compInf_eq {D : D7} (w : InfinitePlace D.host.F) (t' : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.AdelicU.infEmb t' (GlobalTheory.AdelicU.compInf D.host.F D.host.E w y) = GlobalTheory.AdelicU.infProj t' (infPart D y) := by
  have e : GlobalTheory.AdelicU.compInf D.host.F D.host.E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e]
  rfl

theorem absE_of_components {D : D7} (x : (AE D)ˣ) (c : NNReal)
    (hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) = 1)
    (hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) (unitInf D.host.F D.host.E _ x) = c) :
    absE D.host.F D.host.E x = c ^ Fintype.card D.what₂.Tau := by
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one hf
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = c ^ Fintype.card D.what₂.Tau := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw, Finset.prod_const, Finset.card_univ]
  rw [absE_apply, e1, e2, mul_one]

theorem halfMod_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  intro D θ hθ r n t ht α hfin hinf
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hxv : ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = α.1.det := rfl
  have h1 : finPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, hfin, Matrix.det_one]
  have hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det α)) = 1 :=
    fun v => by rw [unitFin_eq_one v _ h1, map_one]
  have hdet : ∀ τ, θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = ((∏ i, t i : ℝ) : ℂ) := by
    intro τ
    have e : θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = (compAt θ τ α.1).det := by
      rw [hxv, ← RingHom.comp_apply, RingHom.map_det]
      rfl
    rw [e, hinf τ, Matrix.det_diagonal, Complex.ofReal_prod]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ (Matrix.GeneralLinearGroup.det α)) = ‖((∏ i, t i : ℝ) : ℂ)‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', ← hdet τ,
      GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (compInf_eq _ t' _)
  have hcard : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.F := by
    rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), IsTotallyReal.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hP : 0 < ∏ i, t i := Finset.prod_pos fun i _ => ht i
  have habs : ((absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det α) : NNReal) : ℝ) =
      (∏ i, t i) ^ (2 * Module.finrank ℚ D.host.F) := by
    rw [absE_of_components _ _ hf hw, hcard, NNReal.coe_pow, NNReal.coe_pow, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP, ← pow_mul]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
  rw [habs, Finset.prod_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  push_cast
  ring

end GlobalTheory.HalfModTorus
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem pairing_gl_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (κ : GL n k) (u y : n → k) :
    ∑ r, (∑ s, u s * κ.val s r) * (∑ t, (κ⁻¹).val r t * y t) = ∑ r, u r * y r := by
  change (u ᵥ* κ.val) ⬝ᵥ ((κ⁻¹).val *ᵥ y) = u ⬝ᵥ y
  rw [dotProduct_mulVec, vecMul_vecMul, Units.mul_inv, vecMul_one]

theorem phase_eq_of_lastMove {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m)
    (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ) :
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  intro hx hx1 he hst
  unfold phase
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rcases Nat.lt_or_ge i.val j with h | h
  · have hxi : x' i = x i := hx _ (by omega) (by omega)
    have hei : e' i = e i := he _ (by omega)
    have hc : colVar x' e' i = colVar x e i := by
      funext r; simp only [colVar, hxi, hei]
    have hch : ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by rw [hxi, hei]
    rw [hch, hc]
    congr 1
    split_ifs with hev
    · have hr : rowVar x' e' (i + 1) = rowVar x e (i + 1) := by
        have hne : (i : ℕ) + 1 ≠ j := by
          intro h'
          rw [show Γ.m - 2 - (i : ℕ) = 1 by omega] at hev
          exact Nat.not_even_one hev
        funext s
        have h1 : x' (i + 1) = x (i + 1) := hx _ hne (by omega)
        simp only [rowVar, h1]
        split_ifs with h3
        · rw [he ⟨(i : ℕ) + 1, h3⟩ (by simpa using hne)]
        · rfl
      rw [hr]
    · rfl
  · obtain ⟨i, hi'⟩ := i
    have hij : i = j := by simp only at h hi; omega
    subst hij
    have h0 : Γ.m - 2 - i = 0 := by omega
    have hch : ∀ z : Matrix (Fin (topRank Γ (i + 1)) ⊕ Fin (Γ.m - 2 - i)) (Fin (topRank Γ i) ⊕ Fin (Γ.m - 2 - i + 1)) k,
        ch z = 0 := by
      intro z
      haveI : IsEmpty (Fin (Γ.m - 2 - i)) := ⟨fun l => by have := l.2; omega⟩
      simp [ch]
    rw [hch, hch, zero_add, zero_add]
    simp only [Fin.val_mk]
    rw [if_pos (by rw [h0]; exact ⟨0, rfl⟩), if_pos (by rw [h0]; exact ⟨0, rfl⟩)]
    have hrow : ∀ (z : ColArgs Γ) (f : Vars Γ) s, rowVar z f (i + 1) s = z (i + 1) (topLast Γ (i + 1 + 1)) s := by
      intro z f s
      simp only [rowVar]
      rw [dite_eq_right (by omega)]
    simp only [hrow, hx1, colVar, Fin.val_mk, hst, map_inv]
    rw [← map_inv]
    have hv : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inl b) = g.val a b := fun _ _ _ => rfl
    have hv2 : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inr b) = 0 := fun _ _ _ => rfl
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hv, hv2, zero_mul, Finset.sum_const_zero, add_zero]
    exact (pairing_gl_inv κ _ _).symm

end GlobalTheory.TopLevelInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.TopLevelInv

theorem phase_eq_of_two_steps : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  intro k _ _ _ _ _ _ Γ j hA x x' e e' hx he h0 hrow hcol
  have hch : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 →
      ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by
    intro i h1 h2; rw [hx i h1 h2, he i h1 h2]
  have hcv : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → ∀ r, colVar x' e' i r = colVar x e i r := by
    intro i h1 h2 r; simp only [colVar]; rw [hx i h1 h2, he i h1 h2]
  have hrv : ∀ n : ℕ, n ≠ j → n ≠ j + 1 → ∀ s, rowVar x' e' n s = rowVar x e n s := by
    intro n h1 h2 s; unfold rowVar
    split_ifs with h
    · rw [hx n h1 h2, he ⟨n, h⟩ h1 h2]
    · rw [hx n h1 h2]
  have hodd : Even (Γ.m - 2 - (j + 1)) ↔ Odd (Γ.m - 2 - j) := by
    rw [show Γ.m - 2 - j = (Γ.m - 2 - (j + 1)) + 1 by omega, Nat.odd_add_one, Nat.not_odd_iff_even]
  have hP1 : (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x' e' (j + 1 + 1) r * colVar x' e' ⟨j + 1, by omega⟩ r else 0)
      = (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x e (j + 1 + 1) r * colVar x e ⟨j + 1, by omega⟩ r else 0) := by
    split_ifs with hE
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hrv (j + 1 + 1) (by omega) (by omega), hcol (hodd.1 hE) r]
    · rfl
  unfold phase
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add (⟨j, by omega⟩ : Fin (Γ.m - 1)) ⟨j + 1, by omega⟩ (by simp [Fin.ext_iff]) ?_]
  · have hch1 := h0
    simp only [Fin.val_mk] at hP1 ⊢
    rw [hP1]
    linear_combination -h0
  · rintro ⟨i, hi⟩ ⟨h1, h2⟩
    simp only [ne_eq, Fin.ext_iff, Fin.val_mk] at h1 h2
    rw [sub_eq_zero, hch ⟨i, hi⟩ h1 h2]
    congr 1
    by_cases hij : i + 1 = j
    · subst hij
      split_ifs with hE
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2, hrow ?_ r]
        rw [show Γ.m - 2 - i = (Γ.m - 2 - (i + 1)) + 1 by omega, Nat.even_add_one, Nat.not_even_iff_odd] at hE
        exact hE
      · rfl
    · split_ifs
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2 r, hrv (i + 1) hij (by omega) r]
      · rfl

end GlobalTheory.TopLevelInv
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

theorem _root_.GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  first | exact @GlobalTheory.HalfModTorus.halfMod_torus | exact GlobalTheory.HalfModTorus.halfMod_torus | (intros; apply GlobalTheory.HalfModTorus.halfMod_torus <;> assumption)

end
end
