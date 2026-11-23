module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle742
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle095
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle745
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory

theorem fibre_restrict_scalar_compat : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), ι ≫ p = q ≫ spMap (Ideal.Quotient.mk m) ≫ chart U → ∀ (V : Z.Opens) (hV : V ≤ p ⁻¹ᵁ U.1) (V' : A.Opens) (hV' : V' ≤ ι ⁻¹ᵁ V) (r : Γ(X, U.1)), (ι.appLE V V' hV').hom ((p.appLE U.1 V hV).hom r) = (q.appLE ⊤ V' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
  intro X Z p U m A q ι h V hV V' hV' r
  have hU : IsAffineOpen U.1 := U.2
  have e0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U.1 := by
    rw [hU.fromSpec_preimage_self]
  have e1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := e0
  have k0 : hU.fromSpec.appLE U.1 ⊤ e0 ≫ (Scheme.ΓSpecIso Γ(X, U.1)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc]
    have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e0).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  have k1 : ∀ x : Γ(X, U.1), ((chart U).appLE U.1 ⊤ e1).hom x = (Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x := by
    intro x
    have := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso Γ(X, U.1)).inv).hom x) k0
    simp only [CommRingCat.comp_apply, CommRingCat.id_apply, Iso.hom_inv_id_apply] at this
    exact this
  have kt : (spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top = (spMap (Ideal.Quotient.mk m)).appTop := by
    dsimp only [Scheme.Hom.appLE]
    exact (congrArg _ ((Sp (Γ(X, U.1) ⧸ m)).presheaf.map_id (Opposite.op ⊤))).trans (Category.comp_id _)
  have k2 : ∀ x : Γ(X, U.1), ((spMap (Ideal.Quotient.mk m)).appLE ⊤ ⊤ le_top).hom
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m x) := by
    intro x
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk m))
    have := congrArg (fun f => f.hom x) hn
    simp only [CommRingCat.comp_apply] at this
    rw [kt]
    exact this.symm
  have hF : ⊤ ≤ (spMap (Ideal.Quotient.mk m) ≫ chart U) ⁻¹ᵁ U.1 :=
    (le_top : ⊤ ≤ spMap (Ideal.Quotient.mk m) ⁻¹ᵁ ⊤).trans
      ((TopologicalSpace.Opens.map (spMap (Ideal.Quotient.mk m)).base).map (homOfLE e1)).le
  have step : ∀ (g : A ⟶ X) (hg : g = q ≫ (spMap (Ideal.Quotient.mk m) ≫ chart U)) (e : V' ≤ g ⁻¹ᵁ U.1),
      (g.appLE U.1 V' e).hom r = (q.appLE ⊤ V' le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ m))).inv.hom (Ideal.Quotient.mk m r)) := by
    rintro g rfl e
    rw [← Scheme.Hom.appLE_comp_appLE q (spMap (Ideal.Quotient.mk m) ≫ chart U) U.1 ⊤ V' hF le_top,
      ← Scheme.Hom.appLE_comp_appLE (spMap (Ideal.Quotient.mk m)) (chart U) U.1 ⊤ ⊤ e1 le_top]
    simp only [CommRingCat.comp_apply]
    rw [k1, k2]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact step _ h _

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieCovol

theorem riemLie_eq_sqrt_index_smul_formLie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → (∀ i, e i ∈ lieLat X.Gm Λ) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt r ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ)) • formLie X.Ψ e := by
  intro E _ _ _ r X Λ x e hr hU hΛ hx he hli
  rw [GlobalTheory.T.riemannian_volume_lie_basis E r X x e hr hx (fun i => ⟨(he i).1, (he i).2.1⟩) hli]
  congr 1
  congr 1
  have h1 := GlobalTheory.T.norm_cm_type_product_sq E X.Ψ X.cmType (Matrix.of fun i j => Matrix.trace (e i * e j)).det
  have h2 := GlobalTheory.T.norm_trace_form_det_index E r X.Gm Λ e hr hΛ he hli
  have h3 := GlobalTheory.T.lie_lattice_dual_index E r X.Gm Λ hr hU hΛ
  rw [h3] at h2
  rw [h2] at h1
  push_cast at h1
  have hn : ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖ = (r : ℝ) ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ) ^ 2 :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hs : Real.sqrt ((r : ℝ) ^ fdeg E) = Real.sqrt r ^ fdeg E := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by positivity)]
  rw [hn, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]

end GlobalTheory.LieCovol
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → haveI := h.finiteDimensional; haveI := h.isGalois; IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  first | exact @GlobalTheory.FrobRestrict.isFrobAt_restrict | exact GlobalTheory.FrobRestrict.isFrobAt_restrict | (intros; apply GlobalTheory.FrobRestrict.isFrobAt_restrict <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  first | exact @GlobalTheory.FockPolGK.pol_locFin_weights | exact GlobalTheory.FockPolGK.pol_locFin_weights | (intros; apply GlobalTheory.FockPolGK.pol_locFin_weights <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.jointShape_unique_and_degW_eq : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ), JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' → (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  first | exact @GlobalTheory.JointShapeUniq.jointShape_unique_deg | exact GlobalTheory.JointShapeUniq.jointShape_unique_deg | (intros; apply GlobalTheory.JointShapeUniq.jointShape_unique_deg <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.lowest_kTypes_jointShape_block_unitary : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamA' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c) ∧ (lamA' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) c ≤ 0)) := by
  first | exact @GlobalTheory.LowestTypes.lowest_types | exact GlobalTheory.LowestTypes.lowest_types | (intros; apply GlobalTheory.LowestTypes.lowest_types <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add (f := _), inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add (f := _), inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a

abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ

abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

variable {ι : Type}

def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det

variable [Fintype ι]

def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1

def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)

def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')

def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ

def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem colSub_minorAt {a d : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (s : Fin a → Fin d) :
    colSub g (minorAt τ s) = (g τ).det • minorAt τ s := by
  unfold minorAt
  rw [AlgHom.map_det]
  have hM : (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).mapMatrix (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) =
      (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)) * (g τ).map C := by
    ext i i'
    simp [colSub, Matrix.mul_apply, mul_comm]
  rw [hM, Matrix.det_mul, show ((g τ).map C).det = C (g τ).det from ((C : ℂ →+* Pol ι d a).map_det (g τ)).symm, smul_eq_C_mul, mul_comm]

theorem colSub_prodMinors {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]

theorem prodMinors_mem_inv {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : prodMinors T ∈ inv a d n :=
  fun g => colSub_prodMinors _ T

theorem colSub_rowSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    colSub g (rowSub κ P) = rowSub κ (colSub g P) := by
  have : (colSub g).comp (rowSub κ) = (rowSub κ).comp (colSub g) := by
    apply MvPolynomial.algHom_ext
    intro y

    simp only [AlgHom.comp_apply, rowSub, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem rowSub_mem_inv {a d : ℕ} {n : ι → ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) {P : Pol ι d a} (hP : P ∈ inv a d n) :
    rowSub κ P ∈ inv a d n := by
  intro g
  rw [colSub_rowSub, hP g, map_smul]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

open Classical

variable {ι : Type} [Fintype ι]

theorem fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by

  rw [Formalism.L2.DIV.fockS_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
  Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [map_mul, map_natCast, RCLike.star_def, Complex.conj_conj]
  ring

theorem fockS_self_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.L2.DIV.fockS f f).re := by
  unfold Formalism.L2.DIV.fockS
  rw [Complex.re_sum]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hf
  have hms : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have key : ∀ k ∈ f.support, (star (f.coeff k) * f.coeff k * (Formalism.L2.DIV.mfact k : ℂ)).re =
      ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ) := by
    intro k _
    rw [RCLike.star_def, mul_comm (starRingEnd ℂ _), Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl key]
  have hpos : 0 < ‖f.coeff m‖ ^ 2 * (Formalism.L2.DIV.mfact m : ℝ) := by
    have : (0 : ℝ) < Formalism.L2.DIV.mfact m := by
      unfold Formalism.L2.DIV.mfact; exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
    positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun k => ‖f.coeff k‖ ^ 2 * (Formalism.L2.DIV.mfact k : ℝ))
    (fun k _ => by positivity) hms)

end GlobalTheory.MinorFrame
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.ColumnInclusionRenaming

theorem fockS_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ ℂ) :
    fockS (rename e f) (rename e g) = fockS f g := by
  classical
  unfold fockS
  rw [support_rename_of_injective he, Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective he h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain e he, coeff_rename_mapDomain e he]
  congr 2
  unfold mfact
  rw [Finsupp.mapDomain_support_of_injective he, Finset.prod_image (fun _ _ _ _ h => he h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective he]

def colIncl {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (r : ℕ) : Fin r × Fin n₀ → Fin r × Fin n₁ :=
  fun v => (v.1, Fin.castLE h v.2)

theorem rename_lpMinor {n₀ n₁ r : ℕ} (h : n₀ ≤ n₁) (s : ℕ) (hr : s ≤ r) (hs : s ≤ n₀) :
    rename (colIncl h r) (lpMinor ℂ s hr hs) = lpMinor ℂ s hr (hs.trans h) := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [colIncl]

theorem rename_hw {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) :
    rename (colIncl h n₁) (hw ℂ h ν) = hw ℂ (le_refl n₁) (rowNu (r := n₁) ν) := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < n₀ := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    have : rowNu (r := n₁) ν s = 0 := by simp [rowNu, hs']
    rw [this, Nat.zero_sub, pow_zero]
  · intro s _
    rw [map_pow, rename_lpMinor]
    have e1 : rowNu (r := n₁) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    have e2 : nuNext (rowNu (r := n₁) ν) (Fin.castLE h s) = nuNext ν s := by
      unfold nuNext rowNu
      by_cases h1 : s.val + 1 < n₀
      · have h2 : s.val + 1 < n₁ := by omega
        simp [h1, h2]
      · simp [h1]
    rw [e1, e2]
    rfl

end GlobalTheory.Proof.ColumnInclusionRenaming
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  first | exact @GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | exact GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | (intros; apply GlobalTheory.AdelicDetSpan.mem_span_detSet_iff <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  first | exact @GlobalTheory.LatOfMult.main | exact GlobalTheory.LatOfMult.main | (intros; apply GlobalTheory.LatOfMult.main <;> assumption)
end
