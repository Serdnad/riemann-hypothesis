module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle125
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle139
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle038
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle138
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle130
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem be_apply_isBes : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv ξ
  obtain ⟨-, C, Ws, hWs, hC⟩ := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  obtain ⟨hlin, -⟩ := GlobalTheory.T.bessel_gap_pairing hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS
  have heq := GlobalTheory.T.bessel_integral_equivariant_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  refine ⟨fun w hw w' hw' => ?_, fun a w hw => ?_, fun g hg m hm w hw => ?_, ‖ξ‖ * C, Ws, hWs, fun w hw => ?_⟩
  · simp only [(hlin v hv w hw w' hw' 0).1, ContinuousLinearMap.add_apply]
  · simp only [(hlin v hv w hw w hw a).2, ContinuousLinearMap.smul_apply]
  · simp only [heq w hw g hg m hm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [mul_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg _)

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem vec_bigPt_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  intro Wp Wq _ _ _ _ _ _ P p H c
  refine ⟨fun hn => ?_, fun ⟨hd, hlt⟩ => ?_⟩
  · show D.vecV p.T.base p.ν' p.m₀ H (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dite_eq_right]
    rintro ⟨hl, hG⟩
    refine hn ⟨fun a => ?_, Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG⟩
    exact (hl.1 (1, c a) (List.mem_ofFn.2 ⟨a, rfl⟩)).2
  · have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
    have hG : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r
        (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := by
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      have hlt' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) := hlt
      nlinarith [mul_lt_mul_of_pos_left hlt' hp]
    have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    refine ⟨hG, fun γ hγ hZ hD => ?_⟩
    have hZ' : Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) := hZ
    have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' γ := by
      rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt c) _ hl hZ']; exact hG
    refine ⟨⟨hγ, hpos⟩, ?_⟩
    show D.vecV p.T.base p.ν' p.m₀ H (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep P.k P.r Wp Wq p.T.base p.ν' p.m₀ H _ hl γ p.hF hG hγ hZ' hD]
    have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt c) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
      Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt c hd)
    obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt c) (P.r + 1) hl.2 hl.1
    rw [hw] at hmono
    rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ hpos hnz (hZ'.trans hmono) H]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.sizes_bound_at_two_first_rows_weights : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  first | exact @GlobalTheory.RunDepth.sizes_bound_two | exact GlobalTheory.RunDepth.sizes_bound_two | (intros; apply GlobalTheory.RunDepth.sizes_bound_two <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicValueToField



theorem sum_map_of_harmA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [Field S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hx, hu, -⟩ := hm
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  dsimp only at hx hu h hh F' hF'
  have hu' : u' = fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ y.u τ i := funext fun τ => funext fun i => hu τ i
  have hx' : x' = spMap (ψ : S →+* S') ≫ y.x := hx
  subst hx'
  subst hu'
  have hh' : h = ptBC (ψ : S →+* S') y.x := Over.OverMorphism.ext hh
  subst hh'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  choose f hf using fun b => hex k (F b)
  obtain ⟨B', x2, e2, -, hF, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (ChartAt.toRaw C)
  let z : FrPt Xo c S' := ⟨_, xo', _, tan', eig', basis', s', gen'⟩
  set_option backward.isDefEq.respectTransparency false in
  let C2 : ChartAt Xo c z :=
    ⟨C.d, B', fun ℓ j => ψ (C.uvec ℓ j), x2, e2, C.wP, MvPowerSeries.map (ψ : S →+* S') C.h,
      ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩,
      ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, C.prim, hga, hrig⟩
  have hg2 : ∀ b, IsGerm z C2.d C2.x C2.B.A.act C2.e C2.wP k (F' b)
      (MvPowerSeries.map (ψ : S →+* S') (f b)) := fun b => hgerm k (F b) (F' b) (f b) (hF' b) (hf b)
  obtain ⟨C3, hex3, hpin3⟩ := hnab.2 S' z
  choose f3 hf3 using fun b => hex3 k (F' b)
  have hI := GlobalTheory.T.harmonicValue_germs_independent_of_chart E H Dw l Xo c hnab.1 S' z C2 C3 k n F' _ f3 hg2 hf3 a P hP
  have e3 : (∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab z k (F' b) (colOf m b)) =
      chartVal C3 k f3 P := by
    unfold chartVal
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun b _ => hpin3 k (F' b) (f3 b) (hf3 b) (colOf m b)
  refine Eq.trans ?_ (hI.trans e3.symm)
  unfold chartVal

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, AlgHom.commutes, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hN := nabMap_holds S S' (ψ : S →+* S') C.d (𝓞 E) C.B B' hF hA C.h C.gauge H.w0 k (f b) (Lt1 Dw) C.uvec
    (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hN
  exact (congrArg ψ (hpin k (F b) (f b) (hf b) (colOf m b))).trans hN.symm

end GlobalTheory.HarmonicValueToField

namespace GlobalTheory

theorem harmonicValue_baseChange_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Field S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S S' _ _ _ _ ψ y y' hm h hh a n P hP N F F' hF'
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  letI : Algebra ℚ S' := ((algebraMap c.F S').comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨M, hM, hMP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have key := HarmonicValueToField.sum_map_of_harmA nab hnab ψ y y' hm h hh a n _ hMP _ (N ^ 2)
    (by push_cast; rfl) F F' hF'
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, map_mul (algebraMap c.F S), map_mul (algebraMap c.F S'),
    _root_.mul_assoc, ← Finset.mul_sum] at key
  rw [map_mul, AlgHom.commutes] at key
  have hu : IsUnit (algebraMap c.F S' (M : c.F)) :=
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hM.ne')).map _
  exact hu.mul_left_cancel key

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem pow_eq_one_of_multilinear {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {j : ℕ} (bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => M) N)
    (hspan : ∀ S : N, S ∈ Submodule.span F {S' | ∃ s, S' = bx s})
    (U : Fin j → Module.End F M) (W : Module.End F N)
    (hW : ∀ s, W (bx s) = bx (fun i => U i (s i)))
    (hU : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ U i ^ m = 1) : ∃ m : ℕ, 1 ≤ m ∧ W ^ m = 1 := by
  classical
  choose m hm hU using hU
  have hp : ∀ (n : ℕ) s, (W ^ n) (bx s) = bx (fun i => (U i ^ n) (s i)) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ', Module.End.mul_apply, ih, hW]
      simp only [pow_succ', Module.End.mul_apply]
  refine ⟨∏ i, m i, Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hm i; omega), LinearMap.ext fun S => ?_⟩
  refine LinearMap.eqOn_span' (s := {S' | ∃ s, S' = bx s}) ?_ (hspan S)
  rintro _ ⟨s, rfl⟩
  rw [hp]
  have : ∀ i, U i ^ (∏ i, m i) = 1 := fun i => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    rw [hc, pow_mul, hU, one_pow]
  simp only [this, Module.End.one_apply]

theorem finOrd_box : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (w : ∀ i, LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F (p i).g.b) (DegPre.lineε k))) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε k))), (∀ i, (w i).IsGen) → w'.IsGen → (∀ (s s₁ : Fin j → Fam D.toPre F k) (S S₁ : Fam D'.toPre F k), (∀ i, PhiRel D.toPre F k (p i) (w i) (s i) (s₁ i)) → IsBoxFam pD F k S s → IsBoxFam pD F k S₁ s₁ → PhiRel D'.toPre F k p' w' S S₁) → ∀ ζ : Fin j → F, (∀ i, FinOrd D F k (p i) (w i) (ζ i)) → FinOrd D' F k p' w' (∏ i, ζ i) := by
  intro hL hL2 hL4 hT V _ _ _ _ j D D' pD F _ _ k hk p' p _ w w' hw hw' hc ζ h
  have hG := hL.globalFns
  obtain ⟨bx, hbx⟩ := GlobalTheory.T.exists_boxFamily_multilinear_map hG V j D.toPre D'.toPre pD F k
  have hspan := GlobalTheory.T.mem_span_boxFamily_powerDegData hL hL2 hL4 hT V j D D' pD F k hk
  simp only [hbx] at hspan
  choose Φ hΦ using fun i => phiFun_of_globalFns hG V _ D F k hk (p i) (w i) (hw i)
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D' F k hk p' w' hw'
  refine (ThetaFinOrd.finOrd_iff p' w' _ Φ' hΦ').2 (pow_eq_one_of_multilinear bx hspan
    (fun i => ζ i • Φ i) _ (fun s => ?_)
    (fun i => (ThetaFinOrd.finOrd_iff (p i) (w i) _ (Φ i) (hΦ i)).1 (h i)))
  have e := (hΦ' _ _).1 (hc s (fun i => Φ i (s i)) _ _ (fun i => (hΦ i _ _).2 rfl)
    ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  simp only [LinearMap.smul_apply]
  rw [← e, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end GlobalTheory
end
end
