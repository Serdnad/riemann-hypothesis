module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.ClassesMeas

theorem nullMeasurableSet_classesOver_framesOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ σ, GoodEmb c σ → ∀ Z : Comp Xo c, NullMeasurableSet (classesOver (V σ) (dict σ) (framesOn (U σ) Z)) (muQ1 (V σ)) := by
  intro D H Dw l Xo c r U V dict hC σ hσ Z
  obtain ⟨hU, ⟨Kf, th, hr, hK, _, hd⟩, _, _⟩ := hC.2 σ hσ
  obtain ⟨d1, d2, ⟨x0, _, d3⟩, d4, _, _⟩ := hd
  haveI : BorelSpace (GA D (V σ)) := ⟨rfl⟩
  let S : Set (U σ).Comp := {k | ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z}
  have key : ∀ g, dict σ g ∈ framesOn (U σ) Z ↔ (dict σ g).1 ∈ S := by
    intro g
    constructor
    · intro h
      exact ⟨(dict σ g).2, h⟩
    · rintro ⟨y, hy⟩
      exact GlobalTheory.T.framePointsOverComponent_open_set D.host.E H Dw l Xo c r U σ hU Z _ y _ (d4 g) hy
  have hP : IsOpen {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    refine Filter.mem_of_superset
      (GlobalTheory.LevelOpen.level_mem_nhds D (V σ) l.M Kf (by have := l.three_le; omega) hK g₀) ?_
    rintro g ⟨k, hk, h, hh, rfl⟩
    obtain ⟨γ, _, e1⟩ := d2 k hk g₀
    obtain ⟨γ', _, e2⟩ := d3 (g₀ * k) h hh
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    show (dict σ (g₀ * k * h)).1 ∈ S
    rw [f2, f1]
    exact hg₀
  have hpre : (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ))) =
      {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    show dict σ (Quotient.mk'' g : AutQ (V σ)).out ∈ framesOn (U σ) Z ↔ _
    rw [key]
    have hrel : QuotientGroup.rightRel (GQ (V σ)) (Quotient.mk'' g : AutQ (V σ)).out g :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨γ', _, e⟩ := d1 _ (inv_mem hrel) g
    have f := congrArg Sigma.fst e
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at f
    rw [f]
  refine MeasurableSet.nullMeasurableSet ?_
  show MeasurableSet (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ)))
  rw [hpre]
  exact hP.measurableSet

end GlobalTheory.ClassesMeas
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareModel

theorem exists_isGood_model_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨hH', hfd'⟩ := GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_and_fundamentalDomain _ (1 : D.host.E) one_ne_zero hJ _ _ hH hfd
  obtain ⟨co, hrat⟩ := GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian B hB X Y r s r' s' hX hY
  have hind := GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum B hB X Y r s r' s' hX hY co hrat
  have hany := GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X Y r s r' s' hX hY co
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  let vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v
      else (hany v).choose
  refine ⟨co, vac, _, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩
  · show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (vac v)
    by_cases h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hany v).choose_spec
  · filter_upwards [hind] with v hv
    show vac v = ind v
    exact if_pos hv

end GlobalTheory.SquareModel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians : ∀ {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∀ {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E), Gm.det ≠ 0 → ∀ u : Matrix (Fin m) (Fin k) (AE D),
      (IsHalf (atPl w 1) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ∧
      (IsHalf (cA D (atPl w 1)) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) := by
  first | exact @GlobalTheory.SplitHalves.halves | exact GlobalTheory.SplitHalves.halves | (intros; apply GlobalTheory.SplitHalves.halves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.heisenbergLatticeVacuum_unique_up_to_scalar : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) (θ : 𝓞 D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr Bs.ψ v → L₁.IsLattice D.host.E → L₂.IsLattice D.host.E →
    (∀ z : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) z →
      (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v ↔
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          Bs.ψ (symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) z γ) = 1)) →
    (θ : D.host.E) + D.sp.cm.sig θ = 1 →
    ∀ φ₀ ψ₀ : (Fin a' × Fin (a + a') → Fv D.host.F v) → ℂ, φ₀ ∈ GlobalTheory.WeilM.SB _ → φ₀ ≠ 0 → (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) →
      ψ₀ ∈ GlobalTheory.WeilM.SB _ → (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  first | exact @GlobalTheory.LatVacUniq.vacuum_unique | exact GlobalTheory.LatVacUniq.vacuum_unique | (intros; apply GlobalTheory.LatVacUniq.vacuum_unique <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertUnitFrame

theorem exists_frame_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  have hX := hG.hV'
  have hd : (G.V'.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  have hJ : IsHermND σ G.V'.Jᵀ :=
    ⟨fun i j => by simp only [Matrix.transpose_apply]; exact hX.herm j i, hd⟩
  have hs : IsSelfDualAt σ G.V'.Jᵀ G.V'.L v :=
    GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B a' G.V' _ _ hB hX v
  have hspan : Submodule.span E (G.V'.L : Set (Fin a' → E)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let a : Fin a' → E := fun i => σ (f (Pi.single i 1))
    let u : Fin a' → E := a ᵥ* G.V'.J⁻¹
    have hu : u ᵥ* G.V'.J = a := by
      simp [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX))]
    have hform (x : Fin a' → E) : form σ G.V'.J u x = σ (f x) := by
      rw [form, Matrix.dotProduct_mulVec, hu, LinearMap.pi_apply_eq_sum_univ f x, map_sum]
      change ∑ i, a i * σ (x i) = _
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have he : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [he]
    have hline (c : E) : c • u ∈ G.V'.L := by
      apply (hX.dual _).2
      intro x hx
      have hx0 : f x = 0 := hf (Submodule.subset_span hx)
      have he : form σ G.V'.J (c • u) x = c * form σ G.V'.J u x := by
        simp [form, smul_dotProduct, smul_eq_mul]
      rw [he, hform, hx0, map_zero, mul_zero]
      exact isIntegral_zero
    have hu0 : u = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
      let coord := (LinearMap.proj i : (Fin a' → E) →ₗ[E] E).restrictScalars (𝓞 E)
      have ht : G.V'.L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / u i) • u, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 E) E := Module.finite_def.mpr (ht ▸ hX.lat.fg.map coord)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have ha : a = 0 := by simpa [hu0] using hu.symm
    apply hf0
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    apply Finset.sum_eq_zero
    intro i _
    have hi : σ (f (Pi.single i 1)) = 0 := congrFun ha i
    have hi' : f (Pi.single i 1) = 0 := (map_eq_zero σ).mp hi
    have he : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := funext fun j => by
      rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
    simp [he, hi']
  obtain ⟨f, hf, ef⟩ := InertChart.exists_frame_antiJ hB.cm hJ hX.lat.fg hspan hw hc hs
  obtain ⟨ϖ, hU⟩ := InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨k, hk, ek⟩ := InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by exact Formalism.UG.cT_one _)
  refine ⟨f * k⁻¹, (InertChart.isFrameAt_mul hf (inv_mem hk)).1, ?_⟩
  have key : Formalism.UG.cT σL (f * k⁻¹).1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f * k⁻¹).1 = 1 := by
    rw [Units.val_mul, Formalism.UG.cT_mul, Units.val_one, Matrix.mul_one] at *
    calc Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f.1 * (k⁻¹).1)
        = Formalism.UG.cT σL (k⁻¹).1 * (Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * f.1) * (k⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL k.1 * (k.1 * (k⁻¹).1) := by
          rw [ef, ← ek]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Formalism.UG.cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Formalism.UG.cT_one, Matrix.one_mul]
  have := congrArg Matrix.transpose key
  simpa [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_map, Matrix.mul_assoc] using this

end GlobalTheory.InertUnitFrame
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicWeilRep_schrodingerModel_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  first | exact @GlobalTheory.WeilSchUnique.weil_unique | exact GlobalTheory.WeilSchUnique.weil_unique | (intros; apply GlobalTheory.WeilSchUnique.weil_unique <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.adelicSchroedinger_schur_commuting_operator_scalar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  first | exact @GlobalTheory.HoweD.AdelicSchur.schur | exact GlobalTheory.HoweD.AdelicSchur.schur | (intros; apply GlobalTheory.HoweD.AdelicSchur.schur <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), PsiUnr B.ψ v → (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V G.W v ↔ ∀ γ ∈ latAtV G.V G.W v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) z γ) = 1)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), φ₀ ≠ 0 → (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₀
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ₀)) →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • φ₀ := by
  first | exact @GlobalTheory.LatVacLine.vacuum_line | exact GlobalTheory.LatVacLine.vacuum_line | (intros; apply GlobalTheory.LatVacLine.vacuum_line <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  first | exact @GlobalTheory.VacUniqInert.vac_unique | exact GlobalTheory.VacUniqInert.vac_unique | (intros; apply GlobalTheory.VacUniqInert.vac_unique <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.local_action_linear_in_vector : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  first | exact @GlobalTheory.LocOpLin.acts_lin | exact GlobalTheory.LocOpLin.acts_lin | (intros; apply GlobalTheory.LocOpLin.acts_lin <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK


theorem _root_.GlobalTheory.T.exists_archOperator_compact_unitaryW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∃ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) := by
  first | exact @GlobalTheory.ArchLocalAct.exists_op_of_KInf | exact GlobalTheory.ArchLocalAct.exists_op_of_KInf | (intros; apply GlobalTheory.ArchLocalAct.exists_op_of_KInf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.AdelicSvN.main | exact GlobalTheory.AdelicSvN.main | (intros; apply GlobalTheory.AdelicSvN.main <;> assumption)
end
