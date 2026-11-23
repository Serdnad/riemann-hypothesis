module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle733
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle734
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaximalIsotropicDoubled
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
import Mathlib.Algebra.Module.Torsion.Prod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle735
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_descent_solution_lift_mod_prism_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ z : Fin d → C.A, (∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) → ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧ (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) := by
  first | exact @GlobalTheory.BSP.lift_solution | exact GlobalTheory.BSP.lift_solution | (intros; apply GlobalTheory.BSP.lift_solution <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_semistable_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  first | (exact @GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (exact GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (intros; apply GlobalTheory.BKLim.WSeed.exists_disc_cocycle  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.frobenius_matrix_relation_discrete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinPreframe_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.pre_bounded_poles | exact GlobalTheory.BKLim.pre_bounded_poles | (intros; apply GlobalTheory.BKLim.pre_bounded_poles <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isCr_of_wSeed_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  first | (exact @GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (exact GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (intros; apply GlobalTheory.BKLim.Frame.isCr_of_wSeed  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_periods_rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BKLim.rational_in_columns_wseed | exact GlobalTheory.BKLim.rational_in_columns_wseed | (intros; apply GlobalTheory.BKLim.rational_in_columns_wseed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Graphs

variable {D : D7}

def graphSub (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Submodule D.host.E ((Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) :=
  LinearMap.range (LinearMap.prod LinearMap.id (Matrix.mulVecLin c))

theorem mem_graphSub {W : HSp D} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    {y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)} : y ∈ graphSub W c ↔ y.2 = c *ᵥ y.1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨y.1, Prod.ext rfl (by simp [h])⟩

theorem cT_eq (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) c = cᴴ := by
  funext i j
  rfl

theorem star_dot (W : HSp D) (c : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (x x' : Fin W.rank → D.host.E) :
    star (c *ᵥ x) ⬝ᵥ W.gram *ᵥ (c *ᵥ x') = star x ⬝ᵥ (cᴴ * W.gram * c) *ᵥ x' := by
  rw [Matrix.star_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

def graphLag (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : Lag W :=
  ⟨graphSub W g, by
    rw [graphSub, LinearMap.finrank_range_of_inj (fun x y h => congrArg Prod.fst h)]
    simp, by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
        W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    rw [cT_eq] at h
    show star x ⬝ᵥ W.gram *ᵥ y = star ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x) ⬝ᵥ
      W.gram *ᵥ ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ y)
    rw [star_dot, h]⟩

theorem graphLag_bot (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    (graphLag W g hg).1.comap (LinearMap.inl D.host.E _ _) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h : (0 : Fin W.rank → D.host.E) = (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ x :=
    mem_graphSub.1 (Submodule.mem_comap.1 hx)
  have h2 := congrArg (((g⁻¹ : GL (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *ᵥ ·) h
  simpa [Matrix.mulVec_mulVec] using h2.symm

theorem herm' (W : HSp D) : W.gramᵀ.map (starRingAut : D.host.E ≃+* D.host.E) = W.gram := by
  have h := GlobalTheory.AutFunCounterexample.gram_herm W
  funext i j
  exact congrFun (congrFun h i) j

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ g : GL (Fin W.rank) D.host.E,
    g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧ Formalism.UG.bc (incA D) g = matHom W (γ : GA D W) := by
  have h : matHom W (γ : GA D W) ∈ HFin (AF D.host.F) D.sp.cm.sig W.gram := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg, e⟩

def ratG (W : HSp D) (γ : GQ W) : GL (Fin W.rank) D.host.E := (exists_rat W γ).choose

theorem ratG_mem (W : HSp D) (γ : GQ W) :
    ratG W γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := (exists_rat W γ).choose_spec.1

theorem mt_ratG (W : HSp D) (γ : GQ W) :
    Formalism.L2.Theta.mt W (γ : GA D W) = (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) := by
  rw [Formalism.L2.Theta.mt, ← (exists_rat W γ).choose_spec.2]
  rfl

theorem bc_injective (W : HSp D) {g g' : GL (Fin W.rank) D.host.E}
    (h : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) =
      (g' : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) : g = g' := by
  exact Units.ext (Matrix.ext fun i j => incA_injective D (congrFun (congrFun h i) j))

theorem graphSub_injective (W : HSp D) {c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : graphSub W c = graphSub W c') : c = c' := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hx : (x, c *ᵥ x) ∈ graphSub W c' := h ▸ mem_graphSub.2 rfl
  exact mem_graphSub.1 hx

theorem isLagFrame_graph (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    IsLagFrame W (graphLag W g hg) (1, (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)) := by
  have h := congrArg (Submodule.map (LinearMap.prod (LinearMap.id : (Fin W.rank → D.host.E) →ₗ[D.host.E] _)
    (Matrix.mulVecLin (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E))))
    (Pi.basisFun D.host.E (Fin W.rank)).span_eq
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  refine Eq.trans ?_ h
  congr 2
  funext j
  ext a <;> simp [Matrix.one_apply, Pi.single_apply]

theorem hr_mem (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) *
      W.gram * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
  show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig)
      ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      W.gram.map (inclR (F := D.host.F) (AF D.host.F)) *
      (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) =
      W.gram.map (inclR (F := D.host.F) (AF D.host.F))
  rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, h]

def ofRat (W : HSp D) (g : GL (Fin W.rank) D.host.E)
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) : GQ W :=
  ⟨(⟨Formalism.UG.bc (incA D) g, hr_mem W g hg⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram),
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

end GlobalTheory.RawLift.Graphs

namespace GlobalTheory.RawLift.Graphs

open GlobalTheory.RawLift.Graphs

theorem graphs : ∀ (D : D7) (W : HSp D), ∃ e : GQ W ≃ {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥},
    ∀ γ : GQ W, ∃ c : Matrix (Fin W.rank) (Fin W.rank) D.host.E, mt W (γ : GA D W) = c.map (incA D) ∧ IsLagFrame W (e γ).1 (1, c) := by
  intro D W
  let f : GQ W → {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} :=
    fun γ => ⟨graphLag W (ratG W γ) (ratG_mem W γ), graphLag_bot W _ _⟩
  have hinj : Function.Injective f := by
    intro γ γ' h
    have h1 : graphSub W (ratG W γ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = graphSub W (ratG W γ') :=
      congrArg (fun Y => Y.1.1) h
    have h2 := graphSub_injective W h1
    have h3 : Formalism.L2.Theta.mt W (γ : GA D W) = Formalism.L2.Theta.mt W (γ' : GA D W) := by
      rw [mt_ratG, mt_ratG, h2]
    exact Subtype.ext (GlobalTheory.AutFunCounterexample.GA_ext W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨Y, hY⟩
    obtain ⟨g, hgU, hgY⟩ := ((GlobalTheory.Doubling.maximal_isotropic_doubled D.host.E starRingAut W.rank W.gram
      (fun x => star_star x) (GlobalTheory.AutFunCounterexample.gram_det_ne W) (herm' W) Y.1 Y.2.1 Y.2.2).2.2).1 hY
    have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := hgU
    refine ⟨ofRat W g hg, Subtype.ext (Subtype.ext ?_)⟩
    have e1 : ratG W (ofRat W g hg) = g := bc_injective W ((mt_ratG W _).symm.trans rfl)
    show graphSub W (ratG W (ofRat W g hg)) = Y.1
    rw [e1]
    ext y
    rw [mem_graphSub]
    exact (hgY y).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ⟨_, mt_ratG W γ, isLagFrame_graph W _ (ratG_mem W γ)⟩⟩

end GlobalTheory.RawLift.Graphs
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

open scoped GlobalTheory.GaugeEx

namespace GlobalTheory.RallisMeas

variable {D : D7}

theorem borelSpace_WO (V W : HSp D) : BorelSpace (WO V W) := ⟨rfl⟩

theorem secondCountable_WO (V W : HSp D) : SecondCountableTopology (WO V W) :=
  inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin V.rank → AE D))

theorem measurable_om_uncurry {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hw : IsWeilDatumO ψ V W χV χW om)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Measurable (fun q : GA D W × WO V W => om (1, q.1) f q.2) := by
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have h := measurable_uncurry_of_continuous_of_measurable (ι := GA D W) (α := WO V W) (β := ℂ)
    (u := fun g w => om (1, g) f w)
    (fun w => (hw.om_cont f hf w).comp (Continuous.prodMk continuous_const continuous_id))
    (fun g => (hw.om_pres (1, g) f hf).cont.measurable)
  exact h

theorem lagTerm_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  intro D ψ V W χV χW om μ 𝓕 hw hμ f₁ f₂ hf₁ hf₂ C
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; simp)
  have hsf : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  have c1 : Continuous (fun u : WO V W => ratMul C.1 u) := by unfold ratMul; fun_prop
  have c2 : Continuous (fun u : WO V W => ratMul C.2 u) := by unfold ratMul; fun_prop
  have m1 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.1) f₁ (ratMul C.1 x.2)) :=
    (measurable_om_uncurry hw hf₁).comp (measurable_fst.fst.prodMk (c1.measurable.comp measurable_snd))
  have m2 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.2) f₂ (ratMul C.2 x.2)) :=
    (measurable_om_uncurry hw hf₂).comp (measurable_fst.snd.prodMk (c2.measurable.comp measurable_snd))
  have hG : Measurable (fun x : (GA D W × GA D W) × WO V W =>
      om (1, x.1.1) f₁ (ratMul C.1 x.2) * star (om (1, x.1.2) f₂ (ratMul C.2 x.2))) :=
    m1.mul (continuous_star.measurable.comp m2)
  exact hG.stronglyMeasurable.integral_prod_right' (ν := μ.restrict 𝓕)

end GlobalTheory.RallisMeas

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem rallis_kernel_step : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨lcV, scV, t2V⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨lcW, scW, t2W⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := hS.haarV
  haveI := hS.haarW
  obtain ⟨hfin, hK⟩ := hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  obtain ⟨B₁, hB₁⟩ := hK f₁ hf₁ φ₁ hφ₁ hc₁
  obtain ⟨B₂, hB₂⟩ := hK f₂ hf₂ φ₂ hφ₂ hc₂
  haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin
  have hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f :=
    fun f hf => hS.weil.om_cont f hf 0
  set μG := νW.restrict 𝓖 with hμG
  set μH := νV.restrict 𝓗 with hμH
  set F : GA D V → GA D W × GA D W → ℂ := fun h p =>
    thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁ :=
      (hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂ :=
      (hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1 :=
      hφ₁.cont.comp (continuous_fst.comp continuous_snd)
    have b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2 :=
      hφ₂.cont.comp (continuous_snd.comp continuous_snd)
    exact (a1.mul b1.star).mul (a2.star.mul b2)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG)) := hFc.aestronglyMeasurable
  have hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG := by
    intro h
    refine ((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul
      hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp [norm_mul]
  have hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG := fun h => (hB₂ h).1
  have hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG) := by
    intro h
    rw [integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]
    unfold upLift
    congr 1
    rw [← hμG]
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1
    funext g
    simp [Complex.star_def]
  have hB₁0 : 0 ≤ B₁ := le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)
  have hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) =
      (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG := by
    intro h
    rw [← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]
    congr 1
    funext p
    simp [hF, norm_mul]
  have hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG)) := by
    rw [integrable_prod_iff hFm]
    refine ⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩
    refine (integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0
  have hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f) := by
    intro h g f
    unfold thetaKO
    rw [show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]
  have hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) =
      fun h => ∫ p, F h p ∂(μG.prod μG) := funext hFh
  refine ⟨fun h => (hB₁ h).1, ?_, ?_⟩
  · show Integrable _ μH
    rw [hup]
    exact hInt.integral_prod_left
  · have hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 *
        ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
      intro p
      have hsw := hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂)
        (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)
      have he := hsw.tsum_eq
      rw [← hμH, tsum_mul_left] at he
      have hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) *
          (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂))) := by
        funext h
        simp only [hF]
        rw [hsplit h p.1 f₁, hsplit h p.2 f₂]
        ring
      rw [hfun, integral_const_mul, ← he]
      ring
    show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _
    rw [hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]
    congr 1
    funext p
    rw [hpt p]

end GlobalTheory.RawLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.coboundary_mem_cocycles_odd_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  first | exact @GlobalTheory.CobCont.main | exact GlobalTheory.CobCont.main | (intros; apply GlobalTheory.CobCont.main <;> assumption)
end
