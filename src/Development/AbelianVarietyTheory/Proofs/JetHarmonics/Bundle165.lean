module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle164
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.RepCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_actLat (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) (v' : Fin n → E) :
    v' ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ ∃ v ∈ Λ.La, γ.mulVec v = v' := by
  simp [UnitaryAdjointCongruence.actLat]






theorem mul_adj {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) : γ * UnitaryAdjointCongruence.adjM γ = 1 :=
  mul_eq_one_comm.1 h

theorem form_adj (γ : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * γ.mulVec w j =
      ∑ j, IsCMField.complexConj E ((UnitaryAdjointCongruence.adjM γ).mulVec v j) * w j := by

  simp only [Matrix.mulVec, dotProduct, UnitaryAdjointCongruence.adjM, Matrix.of_apply, map_sum, map_mul,
  IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (UnitaryAdjointCongruence.actLat γ Λ).Unimod := by
  intro v
  have e : v ∈ (UnitaryAdjointCongruence.actLat γ Λ).La ↔ (UnitaryAdjointCongruence.adjM γ).mulVec v ∈ Λ.La := by
    rw [mem_actLat]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    · intro hv
      exact ⟨_, hv, by rw [Matrix.mulVec_mulVec, mul_adj h, Matrix.one_mulVec]⟩
  rw [e, hΛ]
  constructor
  · intro hv w hw
    obtain ⟨u, hu, rfl⟩ := (mem_actLat _ _ _).1 hw
    rw [form_adj]
    exact hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ((mem_actLat _ _ _).2 ⟨w, hw, rfl⟩)

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Letters

variable (c : Coeff l) {n : ℕ}

theorem push_mem {γ : Matrix (Fin n) (Fin n) E} (h : UnitaryAdjointCongruence.IsUnitaryM γ) {Λ : GenLat E n}
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) :
    UnitaryAdjointCongruence.pushLet c γ P ∈ harmL c (UnitaryAdjointCongruence.actLat γ Λ) a := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  refine ⟨⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n γ P h h1, (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).1 h2,
    (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n γ P fun τ i => a (τ, i)).2 h3⟩, ?_⟩
  have : symO (Dw := Dw) c Λ ≤ (symO c (UnitaryAdjointCongruence.actLat γ Λ)).comap (UnitaryAdjointCongruence.pushLet c γ).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨o, ?_⟩)
      exact (algHom_C (UnitaryAdjointCongruence.pushLet c γ) (o : c.F)).symm
    · exact Subring.subset_closure (Or.inr ⟨σ, i, _, (mem_actLat _ _ _).2 ⟨b, hb, rfl⟩, UnitaryAdjointCongruence.pushLet_letB c γ σ i b⟩)
  exact this h4

end Letters

section Values

variable (Xo : Moduli Dw l) (c : Coeff l)

structure FrameLaws : Prop where
  cover : ChartCoverF Xo c
  test : AllTest Xo c
  bc : ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S),
    ∃ z : FrPt Xo c T, FrMap φ y z

theorem frameLaws : FrameLaws Xo c :=
  have hB := GlobalTheory.allSixLaws.1.secBaseChange
  ⟨GlobalTheory.Frames.chartCoverF_of_secBaseChange hB E H Dw l Xo c, GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c,
    fun S T _ _ _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y⟩

instance (K : Type) [Field K] (p : TRing K) : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

variable {Xo c} {nab : NabV Xo c} {n : ℕ}

end Values

section Clauses

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ}




end Clauses

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

end Cover

section Main

variable [StarRing (𝓞 E)] (Dw) (n : ℕ)

variable {Dw n}

end Main

end GlobalTheory.RepCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (q : ℕ), 1 ≤ q → ∀ (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (s t₀ t : Fam P.D.toPre F q) (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) (p : QkPt P.D.toPre F q) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F), SecTieF I P F xF q σ hh → SecTieF I P F xF q σ' hh' → P.U.toUnifPre.ExpandsG F q σ s → IsSymAct Xo.univ.t.G Xo.univ.t.PP q b hh hh' → PtTieF I P F xF x b → P.ToA F q p x → w.IsGen → FinOrd P.D F q p w ζ → PhiRel P.D.toPre F q p w s t₀ → Fam.IsSmul P.D.toPre F ζ t₀ t → ∃ (u : F) (t' : Fam P.D.toPre F q), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul P.D.toPre F u t t' ∧ P.U.toUnifPre.ExpandsG F q σ' t' := by
  first | exact @GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | exact GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | (intros; apply GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  first | exact @GlobalTheory.HatNF.wordBound_cptCoef | exact GlobalTheory.HatNF.wordBound_cptCoef | (intros; apply GlobalTheory.HatNF.wordBound_cptCoef <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  first | exact @GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | exact GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | (intros; apply GlobalTheory.energy_bound_gfPow_smul_comp_polyOp <;> assumption)
end
