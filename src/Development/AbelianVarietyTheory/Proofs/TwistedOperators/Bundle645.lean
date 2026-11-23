module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle626
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle637
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle627
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle629
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle640
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle635
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle639
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw




namespace GlobalTheory.LastColLat

variable {D : D7}

theorem actO_one_mem_latO (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT))
    (u : WO S T) (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    actO S T 1 h u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    refine GlobalTheory.AdelicLatMove.rankOne_mem_latO S T LS LT a ha _ ?_ _
      ((hh _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL LT α hα t ht))
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact GlobalTheory.AdelicLatMove.pure_mem_hatL LS 1 (one_mem _) s hs
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem actO_inv_mem_latO_iff (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT)) (u : WO S T) :
    actO S T (1 : GA D S)⁻¹ h⁻¹ u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  have hh' : Lev.finE T h⁻¹ ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT) := by
    rw [map_inv]; exact inv_mem hh
  constructor
  · intro hu
    have := actO_one_mem_latO S T LS LT h hh _ hu
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  · intro hu
    rw [inv_one]
    exact actO_one_mem_latO S T LS LT h⁻¹ hh' u hu

end GlobalTheory.LastColLat

namespace GlobalTheory.LastColLat

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem finEmb_stab {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A)
    (hy : Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ)) :
    Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) :=
  GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice d Λ y hy

theorem levRow_stab (S : GridChoice W U) (t : T) :
    ∀ n (hn : 1 ≤ n) (h : n ≤ D.R.m) (k : FinPt G (.grid n D.R.m)), finG (G.V (.grid n D.R.m)) k ∈ S.levRow t n h →
      Lev.finE (G.V (.grid n D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid n D.R.m))) := by
  intro n hn h k hk
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hmem : finG (G.V (.grid (i + 1) D.R.m)) k ∈
      S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hlevel : S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram =
      G.levMax (.grid (i + 1) D.R.m) := by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hlocal (w : Pl D.host.E) (b : ℕ) (hb : b ≠ 0) :
        givenLevel G t w (i + 1, b) =
          GlobalTheory.SplitWeil.KO (Kw w) (Fin ((locGrid G t w).rank (i + 1, b))) := by
      cases b with
      | zero => exact (hb rfl).elim
      | succ _ => rfl
    rw [GridData.levMax]
    exact GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA
      (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
      (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
      (fun w => hlocal w.1 D.R.m hm)
  rw [hlevel, GridData.levMax, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

theorem conj_stab (N : Std G U) {X : Node} (hX : DefNode D.R.m X) (g : FinPt G X)
    (hg : Lev.finE (G.V X) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X))) :
    Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X))) := by
  intro v
  have hu := N.u_lat X hX
  have e : ((Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 : GL _ _) : Matrix _ _ _) *ᵥ v =
      ((Lev.finE (G.V X) (N.u X).1)⁻¹ : GL _ _).1 *ᵥ ((Lev.finE (G.V X) g.1).1 *ᵥ ((Lev.finE (G.V X) (N.u X).1).1 *ᵥ v)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hu, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact hg _

theorem topLast_stab (N : Std G U) (g : FinPt G (.top D.R.m))
    (hg : Lev.finE (G.V (.top D.R.m)) g.1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m))))) :
    Lev.finE (G.V (.top ((lastIx D : ℕ) + 1))) (topLast g).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top ((lastIx D : ℕ) + 1))))) := by
  have key : ∀ n (e : D.R.m = n) (g : FinPt G (.top D.R.m)),
      Lev.finE (G.V (.top D.R.m)) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m)))) →
      Lev.finE (G.V (.top n)) (e ▸ g : FinPt G (.top n)).1 ∈
        Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top n)))) := by
    intro n e g hg
    subst e
    exact hg
  exact key _ (lastIx_succ D) g hg

theorem colPt_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))),
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have h1 := levRow_stab S t D.R.m hm le_rfl k hk
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  have h2 : Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec k).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) := by
    rw [e]; exact finEmb_stab G.sp.topDec _ k h1
  have h3 := conj_stab S.N (X := .top D.R.m) (by simp [DefNode]) _ h2
  have h4 := topLast_stab S.N _ h3
  exact actO_inv_mem_latO_iff _ _ _ _ _ h4 x

end GlobalTheory.LastColLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

theorem isIntw_transport {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X Y P P' : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P'] [Module ℂ P'] (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (ω₀ : GA D V × GA D W →* Module.End ℂ (Y → ℂ))
    (pt : P → (X → ℂ)) (pt₀ : P' → (Y → ℂ)) (e : P ≃ₗ[ℂ] P') (b : Y → X) (It : P' →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (hpt : ∀ φ, pt₀ (e φ) = pt φ ∘ b) (hω : ∀ p F, ω₀ p (F ∘ b) = ω p F ∘ b) (h : IsIntw θ M M' ω₀ pt₀ It) :
    IsIntw θ M M' ω pt (It ∘ₗ e.toLinearMap) := by
  refine { ne := ?_, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro h0
    apply h.ne
    apply LinearMap.ext
    intro φ
    have hφ := congrArg (fun L => L (e.symm φ)) h0
    simpa using hφ
  · intro φ w
    exact h.bdd (e φ) w
  · intro τ g hg φ φ' hφ v
    exact h.eqK τ g hg (e φ) (e φ') (by rw [hpt, hpt, hφ, hω]) v
  · intro τ Y hY φ φ' hd v
    exact h.eqg τ Y hY (e φ) (e φ') (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) v
  · intro τ k hk φ φ' v v' hφ hv
    exact h.invK τ k hk (e φ) (e φ') v v' (by rw [hpt, hpt, hφ, hω]) hv
  · intro τ Y hY φ φ' v v' hd hv
    exact h.invg τ Y hY (e φ) (e φ') v v' (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) hv


open GlobalTheory.FockAdjoint in
theorem ptOf_dag {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} {SV SW : D.what₂.Tau → SPar} (M : DSModel V SV) (M' : DSModel W SW) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) :
    ptOf ψ θ M' M (dag V W g) (jHom (Fr.ofModel M) (Fr.ofModel M') Q) = dag V W (ptOf ψ θ M M' g Q) := by
  set A := Fr.ofModel M
  set B := Fr.ofModel M'
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ V W
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  have hd := L.theta g hg
  show ptF ψ θ B A (dag V W g) (jHom A B Q) = dag V W (ptF ψ θ A B g Q)
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
      dag_smul']
  | add p q hp hq => rw [map_add (f := _), ptF_add, ptF_add, hp, hq, dag_add]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
      ptF_X_mul hψ hθ A B hg]
    dsimp only
    rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hg p), cdag_unitMap,
      aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hg p), dag_smul', Complex.conj_ofReal, smul_smul]
    rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]

open GlobalTheory.FockAdjoint in
theorem jHom_map_conj {S T : HSp D} (A : Fr S) (B : Fr T) (P : PolF D T.rank S.rank) :
    jHom A B (MvPolynomial.map (starRingEnd ℂ) P) = swapHom A B P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [jHom_C, swapHom]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.map_X, jHom_X, map_mul, swapHom_X]

theorem dag_cj {S T : HSp D} (F : WO S T → ℂ) : dag S T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = F ∘ adjO S T := by
  funext y; simp [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

end GlobalTheory.AdjTr


open GlobalTheory.AdjTr in
theorem GlobalTheory.AdjTr.downArrow_transport : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  intro D S T ψ θ χ ω f hθ hW hV
  set A := Fr.ofModel S.M
  set B := Fr.ofModel T.M
  have hstd : IsStdChar D ψ (-1) := hV.1
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hstd S.V T.V
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hV.2.theta
  have hvv := GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace S T ψ θ f hV
  refine ⟨adjRep ω, dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f), χ⁻¹, (swapEquiv A B).toLinearEquiv, ?_,
    fun τ a h => GlobalTheory.Mem.HeckeExp.hasInfExp_inv h, ⟨L.theta _ hvv.theta, ?_, fun τ => GlobalTheory.FockAdjoint.vac_dag hstd hθ L τ
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ) hvv.theta (hvv.vac τ)⟩,
    fun It hIt => ?_⟩
  · exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S.V T.V χ⁻¹ χ⁻¹ (conjRep ω) (GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace ψ S.V T.V χ χ ω hW)
  · intro h0
    apply hvv.ne
    funext x
    have := congrFun h0 (adjO T.V S.V x)
    simp only [dag, GlobalTheory.AdjLawPf.adj_invol, Pi.zero_apply, map_eq_zero] at this
    exact this
  · refine isIntw_transport θ T.M S.M ω.swap (adjRep ω) (GlobalTheory.Grid.fock ψ θ true S T f)
      (ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))) (swapEquiv A B).toLinearEquiv (adjO S.V T.V) It
      (fun φ => ?_) (fun p F => ?_) ((GlobalTheory.Grid.isIntw_iff θ T.M S.M _ _ It).2 hIt)
    · show ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (swapHom A B φ) = _
      rw [← jHom_map_conj, ptOf_dag hstd hθ S.M T.M hvv.theta, ← GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq S T ψ θ f hstd hθ hth, dag_cj]
    · obtain ⟨h, g⟩ := p
      rw [adjRep_apply, WRep.swap_apply]
      funext y
      simp only [Function.comp_apply, GlobalTheory.AdjLawPf.adj_invol]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow.ExtSB

variable {D : D7} {m n : ℕ}

theorem half_of_idem' {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem half_add_nsmul_iff {e : AE D} {t u : Mx D m n} (hu : IsHalf e u) (k : ℕ) :
    IsHalf e (t + k • u) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    linear_combination h1 - (k : AE D) * h2
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    linear_combination h1 + (k : AE D) * h2

theorem smul_add_nsmul (e : AE D) (t u : Mx D m n) (k : ℕ) : e • (t + k • u) = e • t + k • (e • u) := by
  rw [smul_add, smul_comm]

theorem isSBHalf_extFn : ∀ {D : D7} {m n : ℕ} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {Φ : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → IsSBHalf e₀ Λ Φ → IsSBHalf (e₀ + e₁) Λ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) := by
  intro D m n Λ e₀ e₁ Φ h0 h1 h01 hΛ0 hΛ1 hΦ
  obtain ⟨sΦ, k, hk, iΦ, fΦ⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_contra hc
    exact ht (if_neg hc)
  · have hhalf := half_add_nsmul_iff (t := t) hue k
    have hA : Φ (e₀ • (t + k • u)) = Φ (e₀ • t) := by
      rw [smul_add_nsmul]
      exact iΦ _ (hΛ0 u hu) (half_of_idem' h0 u) _
    have hB : halfInd e₁ Λ (e₁ • (t + k • u)) = halfInd e₁ Λ (e₁ • t) := by
      rw [smul_add_nsmul]
      unfold halfInd
      have hm : e₁ • t + k • (e₁ • u) ∈ Λ ↔ e₁ • t ∈ Λ :=
        Λ.add_mem_cancel_right (AddSubgroup.nsmul_mem Λ (hΛ1 u hu) k)
      have hh : IsHalf e₁ (e₁ • t + k • (e₁ • u)) ↔ IsHalf e₁ (e₁ • t) :=
        half_add_nsmul_iff (half_of_idem' h1 u) k
      by_cases hc : e₁ • t ∈ Λ ∧ IsHalf e₁ (e₁ • t)
      · rw [if_pos (And.intro (hm.2 hc.1) (hh.2 hc.2)), if_pos hc]
      · rw [if_neg (fun h => hc ⟨hm.1 h.1, hh.1 h.2⟩), if_neg hc]
    unfold GlobalTheory.CosetRow.extFn
    rw [hA, hB]
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos (hhalf.2 hc), if_pos hc]
    · rw [if_neg (mt hhalf.1 hc), if_neg hc]
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos hc] at ht
      have hΦt : Φ (e₀ • t) ≠ 0 := left_ne_zero_of_mul ht
      have hI : halfInd e₁ Λ (e₁ • t) ≠ 0 := right_ne_zero_of_mul ht
      have hI' : e₁ • t ∈ Λ := by
        unfold halfInd at hI
        by_contra hn
        exact hI (if_neg (fun h => hn h.1))
      have hkt : k • t = k • (e₀ • t) + k • (e₁ • t) := by
        ext i j
        have := hc i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        linear_combination -(k : AE D) * this
      rw [hkt]
      exact Λ.add_mem (fΦ _ hΦt) (AddSubgroup.nsmul_mem Λ hI' k)
    · exact absurd (if_neg hc) ht

end GlobalTheory.CosetRow.ExtSB
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.AvgCol

theorem avg_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL j hj Q Λ
  obtain ⟨hr, huniq⟩ := GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique S hL j hj.le
  let r : GinfC (G.V (.top j)) →* (D.what₂.Tau → GL (Fin (G.V (.top j)).rank) ℂ) :=
    (realIn W.θ S.N.fr (.top j)).comp (GinfC (G.V (.top j))).subtype
  have hrk : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank ∧ 0 < (G.V (.top j)).rank := by
    rw [(node_isV G hL (X := .top j) (show j ≤ D.R.m by omega)).rank,
      (node_isV G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).rank]
    simp only [Node.rank, rankX, rankP, nRk]
    constructor
    · nlinarith
    · omega
  obtain ⟨hab, ha⟩ := hrk
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) :=
    (wtOK_of_defPair G (.top μ0 j) (show j + 1 ≤ D.R.m from hj)).2
  by_cases hex : ∃ κ₀ : Measure (GinfC (G.V (.top j))), κ₀.IsHaarMeasure ∧ IsProbabilityMeasure κ₀
  · obtain ⟨κ₀, h1, h2⟩ := hex
    haveI := h1
    haveI := h2
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional D.what₂.Tau _ _ hab ha (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) hJ
      (GinfC (G.V (.top j))) κ₀ r hr (frChInv W S.N j Q) Λ
    refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
    obtain rfl := huniq κ κ₀ hκ hκp h1 h2
    let ℓ : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₗ[ℂ] ℂ :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS (.top t j)) (G.pT (.top t j)) => ℂ) 0).comp
        ((W.om (.top t j) (G.toPair (.top t j) (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))))).comp
          ((W.fock (.top t j) (movedVec t S d)).comp (frCh W S.N j).toLinearMap))
    have hℓ : ∀ P, ℓ P = W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (frCh W S.N j P))
        (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := fun P => rfl
    have e1 : ∀ k : GinfC (G.V (.top j)),
        W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j))))⁻¹ v) =
          (∏ τ, ((r k τ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ ((nuEnd G (.top μ0 j) τ : ℤ) - (wt G (.top j) τ).detShift) *
              ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
            ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((r k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ) (frChInv W S.N j Q)) *
            Λ (rhoK (wt G (.top j)) (invTrK (r k⁻¹)) v) := by
      intro k
      rw [GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel S hL j hj t d hd Q x k k.2 h, hℓ]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), hΛ' ℓ (realIn W.θ S.N.fr (.top (j + 1)) h) v,
      GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator S hL j hj t d hd x (finOf _ h)]
    have e2 : realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ =
        rhoK (wt G (.top (j + 1))) (invTrK (realIn W.θ S.N.fr (.top (j + 1)) h)⁻¹) := by
      simp only [realAct, MonoidHom.comp_apply, map_inv]
    rw [e2]
    rfl
  · exact ⟨0, fun t _ d _ κ hκ hκp => absurd ⟨κ, hκ, hκp⟩ hex⟩

end GlobalTheory.AvgCol

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastVector_lift_pair_flagLevel_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωX → R.chain_vX → ∀ t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) g0 κ → IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ' → (levChi _ (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ • R.ωX t (κ, κ') (R.vX t) = (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := by
  first | exact @GlobalTheory.StepLaw.last_step_law | exact GlobalTheory.StepLaw.last_step_law | (intros; apply GlobalTheory.StepLaw.last_step_law <;> assumption)
end
