module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaSqMulSqrtEtaSq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Frm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {C M : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup M] [Module C M] {m : ℕ}






end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {x' : Sp T ⟶ X}

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} (y : Z.Pt)

variable {y}




end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

variable {ct}


end GlobalTheory.LocM.Frm
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

end GlobalTheory.ShFam
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Domain

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)

def coW (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j) (Fin j) ℂ :=
  (frameCo X hj f τ).toBlocks₁₁ - moeb (frameCo X hj f τ) 0 * (frameCo X hj f τ).toBlocks₂₁

def coOm (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin (r - j)) (Fin (r - j)) ℂ := (frameCo X hj f τ).toBlocks₂₂

theorem frameCo_eq (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) :
    frameCo X hj f τ = fromBlocks 1 (moeb (frameCo X hj f τ) 0) 0 1 *
      fromBlocks (coW X hj f τ) 0 (frameCo X hj f τ).toBlocks₂₁ (coOm X hj f τ) := by
  rw [fromBlocks_multiply, coW, coOm]
  conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj f τ)]
  simp [moeb_zero, nonsing_inv_mul_cancel_right _ _ (frameCo_isUnit₂₂ X hj hp hf τ)]

theorem isUnit_coOm (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coOm X hj f τ).det :=
  frameCo_isUnit₂₂ X hj hp hf τ

theorem isUnit_coW (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coW X hj f τ).det := by
  have h : IsUnit (frameCo X hj f τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ (det_x0F X τ).isUnit).mul (hf τ).1.isUnit
  rw [frameCo_eq X hj hp hf, det_mul, det_fromBlocks_zero₁₂] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

theorem hodge_co (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : IsOrth X f) (τ : X.Ψ) :
    (coW X hj f τ)ᴴ * (hP (moeb (frameCo X hj f τ) 0))⁻¹ * coW X hj f τ = 1 ∧
      (coOm X hj f τ)ᴴ * hQ (moeb (frameCo X hj f τ) 0) * coOm X hj f τ = 1 := by
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp hf τ
  have h1 := hP_inv_moeb hg (zero_mem_hcDom _ _)
  have h2 := hQ_moeb hg (zero_mem_hcDom _ _)
  rw [jW, e] at h1
  rw [kapQ, e, Matrix.mul_zero, zero_add] at h2
  exact ⟨h1.trans (by simp [hP]), h2.trans (by simp [hQ])⟩

end Frames

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance FinalTheorems.smooth (s : FinalTheorems S κ) : SmoothOfRelativeDimension S.Dw.dim (genStr s.T.Z) := s.T.smooth

abbrev ToroidalCompactificationData (s : FinalTheorems S κ) : Type := OddPrimesWithRootsOfUnity s.T.Z

theorem Sig.mult_psi (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (L.ψ t).1 = j :=
  (if_pos (L.ψ t).2).trans S.p_eq

theorem Sig.mult_conj (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (conjEmb (L.ψ t).1) = N - j :=
  (if_neg (GlobalTheory.AllWt.conj_not_mem (L.ψ t))).trans (by have := S.p_eq; have := S.rank_eq; omega)

namespace FinalTheorems

variable (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)

abbrev fd : Data D.host.E N := (s.U κ.σ₀).X k


include s in
theorem j_le : j ≤ N := le_of_isUnf _ s.isUnf S.p_eq

abbrev lab : D.what₂.Tau ≃ (s.fd k).Ψ := cmEquiv _ s.isUnf L.ψ k

abbrev zOf (f : (s.fd k).dom) : Pt D.what₂.Tau j (N - j) := domPt (s.fd k) s.j_le (s.lab L k) f.1

def framePt (f : (s.fd k).dom) : CxPts (genStr s.T.Z) κ.σ₀ := cxPt s.T.Z ((s.U κ.σ₀).un k f)

def lieFrame (f : (s.fd k).dom) : EigFrame s.T.Z κ.σ₀ ((s.framePt k f).1 ≫ genι s.T.Z) :=
  cxFrame s.T.Z ((s.U κ.σ₀).un k f)


open Classical in
def frameOver (z : Pt D.what₂.Tau j (N - j)) : (s.fd k).dom :=
  if h : ∃ f, s.zOf L k f = z then h.choose else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩

def toCpt (z : Pt D.what₂.Tau j (N - j)) : CxPts (genStr s.T.Z) κ.σ₀ := s.framePt k (s.frameOver L k z)

end FinalTheorems

variable {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (L : CmList A)

def ToroidalCompactificationData.gramW (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  (x.gram (s.framePt k f) (s.lieFrame k f) (L.ψ t).1).submatrix
    (Fin.cast (S.mult_psi L t).symm) (Fin.cast (S.mult_psi L t).symm)

def ToroidalCompactificationData.gramOm (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((hodgeC (s.fd k) (s.lab L k) t : ℂ) ^ 2) •
    (dualGram (x.gram (s.framePt k f) (s.lieFrame k f) (conjEmb (L.ψ t).1))).submatrix
      (fun a => Fin.cast (S.mult_conj L t).symm a.rev) (fun a => Fin.cast (S.mult_conj L t).symm a.rev)

def ToroidalCompactificationData.metW (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  ((coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramW L k (s.frameOver L k z) t *
    (coW (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

def ToroidalCompactificationData.metOm (k : s.Comp) (z : Pt D.what₂.Tau j (N - j)) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹)ᴴ * x.gramOm L k (s.frameOver L k z) t *
    (coOm (s.fd k) s.j_le (s.frameOver L k z).1 (s.lab L k t))⁻¹

structure IsBdOf (B : s.Bd L) : Prop where
  m_eq : ∀ k, (B k).m = x.m
  nrm : ∀ k i, ∀ z ∈ DomI D.what₂.Tau j (N - j), (B k).nrm i z = x.nrm κ.σ₀ (Fin.cast (m_eq k) i) (s.toCpt L k z)
  kae : ∀ k W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j),
    s.toCpt L k z ∈ W → ∀ ξ, ((B k).kae z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ
  cst : ∀ k, (B k).cst = x.cst
  metW : ∀ k f t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metW (s.zOf L k f) t *
    coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t
  metOm : ∀ k f t, (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metOm (s.zOf L k f) t *
    coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t

namespace IsBdOf

variable {x L} {B B' : s.Bd L} (h : IsBdOf x L B) (k : s.Comp) {z : Pt D.what₂.Tau j (N - j)}
include h

end IsBdOf

end Domain

end GlobalTheory.ShFam
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier
open GlobalTheory.ShFam.Descent GlobalTheory.FlatLine

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Frame

variable (Z : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (P : FrPt Xo c R)

def frameOf : EigFrame Z (algebraMap c.F R) (GlobalTheory.AllWt.ptF P ≫ Z.j) := (exists_tie_frame P rfl).choose

variable {Z P}

end Frame

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def CoordAt {k : Type} [Field k] [Algebra c.F k] (P : FrPt Xo c k) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ p : Sp k ⟶ Y.Y.X, p ≫ Y.π = GlobalTheory.AllWt.ptF P ≫ Z.jQ ∧ IsCoord Y p (frameOf Z P) n σ a

def CoordAtC {ι : c.F →+* ℂ} (P : FrPt Xo c (CAt ι)) (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : ℂ) : Prop :=
  letI := ι.toAlgebra; CoordAt (k := ℂ) Y P n σ a

variable {Y}

variable {r : ℕ}

end Free

end GlobalTheory.ShFam.Pad
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.TorCheck

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem minVal_eval (B : X → X → ℝ) : (InvFun.minVal O).eval X B = sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  change sInf _ = _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, map_zero]
  exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩

theorem minVal_linearOn (γ : LinearMap.BilinForm ℤ X) : (InvFun.minVal O).LinearOn ![γ] := by
  intro c hc
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, InvFun.evalZ, minVal_eval, map_zero, Int.cast_zero, mul_zero,
    LinearMap.zero_apply]
  rcases (hc 0).eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul]
    convert Real.sInf_empty
    simp [eq_comm]
  · rw [← smul_eq_mul (c 0) (sInf _), ← Real.sInf_smul_of_nonneg (hc 0)]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      exact ⟨_, ⟨⟨y, rfl⟩, fun e => hx (by rw [e, mul_zero])⟩, rfl⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hx⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, mul_ne_zero h.ne' hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

end GlobalTheory.LocM.TorCheck
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix MeasureTheory Set Complex
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ChernReg

section Flat

variable {d : ℕ}

def polMat (q : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ := fun k l =>
  (q (Pi.single k 1 + Pi.single l 1) - q (Pi.single k 1 - Pi.single l 1) +
    I * q (Pi.single k 1 + I • Pi.single l 1) - I * q (Pi.single k 1 - I • Pi.single l 1)) / 4

def christoffel (b : V d → Matrix (Fin d) (Fin d) ℂ) (z ξ : V d) : V d :=
  WithLp.toLp 2 ((ξ.ofLp ᵥ* Matrix.of fun k l => del (fun v => b v k l) z ξ) ᵥ* (b z)⁻¹)

def jet (b : V d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) : V d × V d → V d :=
  n.rec Prod.fst fun _ f q => del f q (q.2, -christoffel b q.1 q.2)

variable (b : V d → Matrix (Fin d) (Fin d) ℂ)

def cutoff (t : ℝ) : ℝ := if t < 1 then ((1 - t) ^ 2)⁻¹ * Real.exp (t - 1)⁻¹ else 0

def mean (q f : (Fin d → ℂ) → ℝ) : ℝ := (∫ ξ, f ξ * cutoff (q ξ)) / ∫ ξ, cutoff (q ξ)

section Mass

variable {q : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
  (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ)
include hc hh hp

end Mass

end Flat

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

abbrev ChartMap (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → CxPts p σ

def matIn (a : ChartForm p σ d) (c : AlgChart p σ d) (v : V d) : Matrix (Fin d) (Fin d) ℂ := polMat (a c (c.e.symm v))

structure IsExph (a : ChartForm p σ d) (E : ChartMap p σ d) : Prop where

  trans : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ)

  cont : ∀ c : AlgChart p σ d, ContinuousOn (fun q : V d × V d => E c (c.e.symm q.1) q.2.ofLp) (c.e.target ×ˢ univ)

  smooth : ∀ c c' : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × V d => c'.e (E c (c.e.symm q.1) q.2.ofLp))
    {q | q.1 ∈ c.e.target ∧ E c (c.e.symm q.1) q.2.ofLp ∈ c'.e.source}

  zero : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, E c y 0 = y

  jets : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ (ξ : V d) (n : ℕ),
    iteratedDeriv n (fun t : ℝ => c.e (E c y (t • ξ.ofLp))) 0 = jet (matIn a c) n (c.e y, ξ)

def ConjComm (j : CxPts p σ' → CxPts p σ) (E : ChartMap p σ d) (E' : ChartMap p σ' d) : Prop :=
  ∀ (c : AlgChart p σ d) (c' : AlgChart p σ' d),
    (∀ w ∈ c'.e.source, j w ∈ c.e.source → ∀ i, c'.e w i = starRingEnd ℂ (c.e (j w) i)) →
    ∀ z ∈ c'.e.source, j z ∈ c.e.source → ∀ ξ, j (E' c' z ξ) = E c (j z) (star ξ)

def rhoIn (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (c : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) : ℝ :=
  mean (a c y) fun ξ => ψ (E c y (t • ξ))

structure IsRegConst (a θ : ChartForm p σ d) (Ψ : CxPts p σ → ℝ → ℝ) (A K δ : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  K_nonneg : 0 ≤ K
  δ_pos : 0 < δ
  smooth : ∀ c : AlgChart p σ d, ContDiffOn ℝ ∞ (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖)
    (c.e.target ×ˢ {w | 0 < ‖w‖ ∧ ‖w‖ < δ})
  mono : ∀ y, MonotoneOn (fun t => Ψ y t + K * t ^ 2) (Ioo 0 δ)
  hess : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ → ∀ (ξ : V d) (η : ℂ),
    -(A * (‖w‖ * deriv (fun t => Ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
        K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
      θ c y ξ.ofLp + (leviForm (fun q : V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

variable {a : ChartForm p σ d} {E : ChartMap p σ d} {R : AnRead p σ d}

variable [SmoothOfRelativeDimension d p]

def rho (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ) (y : CxPts p σ) (t : ℝ) : ℝ :=
  rhoIn a E ψ (AlgChart.exists_mem_source (D := d) y).choose y t



end Manifold

end GlobalTheory.ChernReg
end
end
