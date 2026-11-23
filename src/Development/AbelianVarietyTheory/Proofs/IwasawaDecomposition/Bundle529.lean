module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open TopologicalSpace
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.SharedLaws

section Top

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem exists_finite_generic {F : Set X} (hF : IsClosed F) :
    ∃ G : Set X, G.Finite ∧ G ⊆ F ∧ ∀ x ∈ F, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose η hη using fun t (ht : t ∈ S) => QuasiSober.sober (hi t ht) (hc t ht)
  haveI := hS.to_subtype
  refine ⟨Set.range fun t : S => η t.1 t.2, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t.1, t.2, (hη t.1 t.2).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη t ht).specializes hx⟩

theorem mem_of_maximal {x : X} (hx : ∀ x' : X, x' ⤳ x → x' = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    x ∈ U := by
  obtain ⟨G, hG, -, h⟩ := exists_finite_generic (isClosed_univ (X := X))
  have hC : IsClosed (⋃ g ∈ G \ {x}, closure ({g} : Set X)) :=
    (hG.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨y, hy, hyU⟩ := hd.inter_open_nonempty _ hC.isOpen_compl ⟨x, fun hm => by
    obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 hm
    exact hg.2 (hx g (specializes_iff_mem_closure.2 hgx))⟩
  obtain ⟨g, hg, hgy⟩ := h y trivial
  by_cases e : g = x
  · exact (e ▸ hgy).mem_open hU hyU
  · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, e⟩, specializes_iff_mem_closure.1 hgy⟩) hy

end Top

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isProper_toroidalModel_structureMap (Z : Mdl Y i₀) : IsProper Z.s := by
  have := isProper_str (Z.i.c.V W) Z.n
  unfold Pre.s
  infer_instance

theorem noetherianSpace (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : NoetherianSpace Z.X := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (mem_nonunits_V Z.i.c hp hW)).1
  haveI := isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  haveI : IsNoetherian Z.X := {}
  infer_instance

theorem abP_of_isGenP (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) (hx : Z.isGenP x) :
    Z.abP x := by
  haveI := noetherianSpace hp hW Z
  have ho : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2
  obtain ⟨z, hz⟩ := mem_of_maximal hx ho Z.dense
  have : (Y Z.i).jQ z ∈ pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype) ⁻¹' abLocus (Y Z.i).t.G := by
    rw [(Y Z.i).ab_gen]
    exact ⟨z, rfl⟩
  unfold Mdl.abP
  rw [← hz]
  exact this

end Free

end GlobalTheory.LocM.SharedLaws
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points

namespace GlobalTheory.AmpleModelPos

theorem isGenerated_tens {X : Scheme.{0}} {A B : LB X} (hA : IsGenerated A) (hB : IsGenerated B) :
    IsGenerated (tens A B) := by
  obtain ⟨a, s, hs⟩ := hA
  obtain ⟨b, t, ht⟩ := hB
  refine isGenerated_of_finite (fun q : Fin a × Fin b => EndOnTorsion.tensSec (s q.1) (t q.2))
    (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (EndOnTorsion.nonzeroLocus_tensSec (s i) (t j)).ge ⟨hi, hj⟩⟩

section Pull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D N : ℕ}

end Pull

end GlobalTheory.AmpleModelPos
end
end

section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CuspFieldChange

open GlobalTheory.FieldBC GlobalTheory.SecFieldChange
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of evR_of_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

variable {c c₀ : Coeff l} (hle : c₀.F ≤ c.F)

theorem eq_sum_of_isBC {m : ℕ} {f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf' : f' ∈ sec Xo c a n)
    {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀} (h : IsBC hle f' as fs) : f' = ∑ i, as i • rulBC hle (fs i) := by
  funext q y
  letI := resAlg hle q.R
  rw [val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def]
  rfl

theorem cusp_unfBC_eq_span {r : ℕ} (U : ∀ σ : c₀.F →+* ℂ, Unf Xo c₀ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (unfBC hle U) a n = Submodule.span c.F (rulBC hle '' (cusp Xo c₀ U a n : Set (Rul Xo c₀))) := by
  refine le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, as, fs, hfs, h⟩ := cuspBC_holds hle U a n f' hf'
    rw [eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf

theorem linearIndependent_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {v : Fin m → Rul Xo c₀}
    (hv : ∀ i, v i ∈ sec Xo c₀ a n) (hi : LinearIndependent c₀.F v) :
    LinearIndependent c.F (fun i => rulBC hle (v i)) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c₀ :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))
  have hBC : HasBC Xo c₀ := hasBC_of hS
  letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro g hg i
  refine (Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_
  refine hi (fun j => lam (g j)) ?_ i
  funext p y
  have hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R) := fun x => ext_tower x
  obtain ⟨z, hz⟩ := hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y
  have h1 := evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))
  have h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0 := evalAt_zero _ _ _
  rw [hg, h0] at h1
  have h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y) := fun j => by
    rw [((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext,
      evR_of_map hWD (hv j).1 hz]
  simp only [h2] at h1
  have h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) =
      (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R) := fun j => by
    show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) :
      TensorProduct c₀.F c.F p.R) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y) :=
    h1.trans (Finset.sum_congr rfl fun j _ => h3 j)
  have h5 := congrArg (coord lam p.R) h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h5
  simp only [coord_tmul] at h5
  rw [Finset.sum_apply, Finset.sum_apply]
  exact h5.symm

end GlobalTheory.CuspFieldChange
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSymm

section Split

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def chernRootsOver : MvPolynomial (ι × ℕ) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R x.2)

variable {m} [DecidableEq ι] (τ₀ : ι)

def rootSplit : Root m ≃ Fin (m τ₀) ⊕ Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) :=
  GlobalTheory.InnerAutomorphism.sigmaSplit (fun τ => Fin (m τ)) τ₀

def splitEquiv : MvPolynomial (Root m) R ≃ₐ[R]
    MvPolynomial (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :=
  (renameEquiv R (rootSplit τ₀)).trans (sumAlgEquiv R _ _)

theorem splitEquiv_X_self (i : Fin (m τ₀)) :
    splitEquiv R τ₀ (X (⟨τ₀, i⟩ : Root m)) = X i := by
  have e : rootSplit τ₀ (⟨τ₀, i⟩ : Root m) = Sum.inl i := GlobalTheory.InnerAutomorphism.sigmaSplit_self (fun τ => Fin (m τ)) τ₀ i
  simp [splitEquiv, e]

theorem splitEquiv_X_ne {τ : ι} (h : τ ≠ τ₀) (i : Fin (m τ)) :
    splitEquiv R τ₀ (X (⟨τ, i⟩ : Root m)) = C (X ⟨⟨τ, h⟩, i⟩) := by
  have e : rootSplit τ₀ (⟨τ, i⟩ : Root m) = Sum.inr ⟨⟨τ, h⟩, i⟩ := GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne (fun τ => Fin (m τ)) h i
  simp [splitEquiv, e]

theorem splitEquiv_symm_X (i : Fin (m τ₀)) :
    (splitEquiv R τ₀).symm (X i) = X (⟨τ₀, i⟩ : Root m) := by
  rw [AlgEquiv.symm_apply_eq, splitEquiv_X_self]

theorem splitEquiv_symm_C (c : MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :
    (splitEquiv R τ₀).symm (C c) = rename (fun y => (⟨y.1.1, y.2⟩ : Root m)) c := by
  rw [AlgEquiv.symm_apply_eq]
  induction c using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C]
    change _ = splitEquiv R τ₀ (algebraMap R _ r)
    rw [AlgEquiv.commutes]; rfl
  | add p q hp hq => simp [map_add (f := _), ← hp, ← hq]
  | mul_X p y hp =>
    simp only [map_mul, rename_X]
    rw [← hp, splitEquiv_X_ne R τ₀ y.1.2]

theorem splitEquiv_symm_esymm (j : ℕ) :
    (splitEquiv R τ₀).symm (esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) j) =
      chernRootsOver R m (X (τ₀, j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [chernRootsOver, esymm, map_sum, map_prod, splitEquiv_symm_X]

theorem splitEquiv_rename_update (σ : Equiv.Perm (Fin (m τ₀))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)) S) = rename σ (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)))) =
      ((rename σ).restrictScalars R).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, Function.update_of_ne h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem splitEquiv_rename_rest (w' : ∀ τ : {τ // τ ≠ τ₀}, Equiv.Perm (Fin (m τ.1))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)) S) =
      MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)))) =
      (mapAlgHom (rename (Equiv.sigmaCongrRight w'))).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem rename_chernRootsOver (T : MvPolynomial ({τ // τ ≠ τ₀} × ℕ) R) :
    rename (fun y : Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) => (⟨y.1.1, y.2⟩ : Root m))
      (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1) T) =
      chernRootsOver R m (rename (Prod.map Subtype.val id) T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [chernRootsOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    congr 1
    simp [chernRootsOver, rename_rename]
    rfl

end Split

theorem mem_range_chernRootsOver (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ) (S : MvPolynomial (Root m) R),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    S ∈ (chernRootsOver R m).range := by
  induction n with
  | zero =>
    intro ι _ _ hc R _ m S _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [eq_C_of_isEmpty S]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro ι _ _ hc R _ m S hS
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    let f : Fin (m τ₀) → MvPolynomial (Fin (m τ₀)) R' := fun i => esymm (Fin (m τ₀)) R' (↑i + 1)
    have hsym : splitEquiv R τ₀ S ∈ symmetricSubalgebra (Fin (m τ₀)) R' := by
      rw [mem_symmetricSubalgebra]
      intro σ
      rw [← splitEquiv_rename_update, hS]
    obtain ⟨T, hT⟩ := esymmAlgHom_fin_surjective R' (m := m τ₀) (n := m τ₀) le_rfl ⟨_, hsym⟩
    have hT' : aeval f T = splitEquiv R τ₀ S := by
      rw [← esymmAlgHom_apply, hT]
    have hcoef : ∀ d, AddMonoidAlgebra.coeff T d ∈ (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1)).range := by
      intro d
      apply ih _ hc' R
      intro w'
      have hinv : MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom T = T := by
        apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
        apply Subtype.ext
        rw [esymmAlgHom_apply, esymmAlgHom_apply]
        change aeval f _ = aeval f T
        rw [hT', ← hS (fun τ => if h : τ = τ₀ then 1 else w' ⟨τ, h⟩), splitEquiv_rename_rest, ← hT',
          aeval_def, aeval_def, algebraMap_eq, eval₂_map, eval₂_comp_left, map_comp_C]
        congr 1
        funext i
        exact (map_esymm _ _ _ _).symm
      have := congrArg (AddMonoidAlgebra.coeff · d) hinv
      rwa [coeff_map] at this
    let k : MvPolynomial (Fin (m τ₀)) R' →+* MvPolynomial (Root m) R :=
      (splitEquiv R τ₀).symm.toRingEquiv.toRingHom
    have hSE : S = k (eval₂ C f T) := by
      change S = (splitEquiv R τ₀).symm _
      rw [← algebraMap_eq, ← aeval_def, hT', AlgEquiv.symm_apply_apply]
    have key : k (eval₂ C f T) = eval₂ (k.comp C) (k ∘ f) T := eval₂_comp_left k C f T
    rw [hSE, key, eval₂_eq]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · obtain ⟨Tc, hTc⟩ := (AlgHom.mem_range _).mp (hcoef d)
      rw [RingHom.comp_apply, ← hTc]
      change (splitEquiv R τ₀).symm (C _) ∈ _
      rw [splitEquiv_symm_C, rename_chernRootsOver]
      exact AlgHom.mem_range_self _ _
    · change (splitEquiv R τ₀).symm (esymm _ _ _) ∈ _
      rw [splitEquiv_symm_esymm]
      exact AlgHom.mem_range_self _ _

theorem exists_chernRoots_eq_of_blockSymmetric : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  intro ι _ m S hS
  classical
  obtain ⟨R, hR⟩ := (AlgHom.mem_range _).mp (mem_range_chernRootsOver _ ι rfl ℝ m S hS)
  exact ⟨R, hR⟩

end GlobalTheory.BlockSymm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


theorem _root_.GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) → ∀ (sS : Fam S) (sT : Fam T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) ΛS ΛS → GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T k') ΛT ΛT → ∀ x y : (AE D)ˣ, FinUnit x → FinUnit y → IsDetRoot S k x → IsDetRoot T k' y → om (k, k') f = ((((χT x)⁻¹ * χS y : Circle)) : ℂ) • f := by
  first | exact @GlobalTheory.FinVac.om_vacuum_finite | exact GlobalTheory.FinVac.om_vacuum_finite | (intros; apply GlobalTheory.FinVac.om_vacuum_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ t : RowsT K w x.o.Z P.Wt x.s.p0, t.r = x.rowsAre hη → Nonempty (RXs t) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | exact GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state | (intros; apply GlobalTheory.Mem.R3.Rw.Ties.rxs_of_state <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem rootDiscr_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  intro ι _ m
  unfold rootDiscr
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [sub_ne_zero]
  intro h
  have h2 := X_injective (σ := Root m) (R := ℝ) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
  exact (Finset.mem_Iio.mp hi).ne h2.symm

end GlobalTheory.GoodMetric
end
