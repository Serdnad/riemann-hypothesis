module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle043
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle055
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle084
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle083
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle065
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobi
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_inBasis_shares_inContain : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (G₀ : GlobalFamilyData (recPlusN h j hj n) ka wL wF) (Tn : ℕ) (CR c : ℝ) (S : Scal n.base), addL wF wL Tn = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn → Nonempty (ArchAt h j G₀.w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → LatAt n.base j ka → (∃ β : ℝ, ShortG (recPlusN h j hj n) ((recPlusN h j hj n).wF0 wL wF) ((recPlusN h j hj n).Thc S.s0 ((recPlusN h j hj n).wF0 wL wF)) β) → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → ∃ (del : ℕ) (th' : Fin del → n.base.Cusp j wF), (∀ i, th' i ∈ Sh) ∧ ∀ rz alz th0 zc rq th iet et, (∀ la, InBasis (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la) ∧ ShareRd (D := D) (j := j) Tn del ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) S Tn ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoP (D := D) (j := j) Tn (WeightFamilies.rhoP n.base CR Tn c j ka) ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ∀ la, InContainMR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la S CR Tn c := by
  intro D T h j hj n ka wL wF G₀ Tn CR c S hka hd2 hT hArch hRd hMgg hLat hShort Sh hSh

  obtain ⟨R, t, δ, xs, hgen, hA⟩ :=
    GlobalTheory.T.analyticFacts_of_thetaData_on_models D T h j hj n G₀.N ka wL wF G₀.w Tn CR c hka hArch hRd hMgg
      (GlobalTheory.T.maximalCusps_noLowCoefficient_iff_fourierJacobi D T h j hj ka CR (Tn : ℝ) c)

  obtain ⟨θ, hθS, hθ⟩ :=
    exists_valueBasis_in_spanning D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn _ δ xs hA Sh hSh
  refine ⟨δ, θ, hθS, ?_⟩
  intro rz alz th0 zc rq th iet et
  have hdT : WeightFamilies.dimY D j < Tn := by nlinarith
  have hd0 : 0 < WeightFamilies.dimY D j := by omega

  have hA' : AnFacts R (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et).w t ka wF Tn
      (WeightFamilies.MggK n.base CR Tn c j ka) xs := hA
  have hB : ∀ la, InBasis (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) la := fun la =>
    (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D n.base _ j (recPlusN h j hj n) ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hgen hA' hka la).2 ⟨hθ, rfl⟩

  obtain ⟨β, Sg, hSg, hspan, -⟩ := hShort
  have hle := Submodule.span_mono (R := n.base.KO) hSg
  rw [hspan] at hle
  have hTop := top_le_iff.mp hle
  obtain ⟨la₀⟩ := nonempty_heightOneSpectrum_ringOfIntegers n.base.KO
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · exact shareRd_of_inBasis D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hdT hd0 hLat ⟨la₀, hB la₀⟩
  · exact shareRhoR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hd2 hT hLat S
  · exact shareRhoP_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn CR c δ xs hA hd2 hT hLat
  · intro la
    exact Contain.inContainMR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn CR c δ xs hgen hA' hka hdT.le S hTop la (hB la)

end GlobalTheory.Shares
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_net_max_at_goodEmb : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ NN : Finset (FPt (T.U j σ).X), NN.Nonempty ∧ (∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∃ p ∈ NN, supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) P ≤ 4 * ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w) w.n p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h hG large₂ j hj w hw hL hrn hf σ hσ

  have hne0 : Nonempty (T.U j σ).Comp := ⟨(T.dict j σ 1).1⟩
  obtain ⟨-, hlrd, hd, hcc, hlf, -, -, -, hn⟩ := id hw
  obtain ⟨-, -, -, -, -, hfdeg, hdE, -, hfr, hf1, -, -, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hd hcc
  obtain ⟨e, M, wg, hM1, hMl, hwg, hwgl, -, hk⟩ := GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T h hG large₂ j hj w hw hL hrn σ hσ
  have hcard := GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w hw hL hrn hf σ hσ
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by linarith
  have hr1 : 1 ≤ D.R.r := le_trans hf1 hfr
  have hF1 : (1 : ℝ) ≤ (fdeg D.host.E : ℝ) := by rw [hfdeg]; exact_mod_cast hf1
  have hZ : Zb D large₂ = (fdeg D.host.E : ℝ) * D.R.r * large₂.sc.L := by rw [hfdeg]; rfl

  have hlogr : Real.log (D.R.r : ℝ) ≤ large₂.sc.L := by
    refine le_trans (Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrn)) hn
  have hlogf : Real.log (fdeg D.host.E : ℝ) ≤ 2 * large₂.sc.L := by rw [hfdeg]; exact hlf
  obtain ⟨NN, hne, hP, hlog⟩ :=
    GlobalTheory.NetMax.exists_net_all_components_max D.host.E D.R.r (T.U j σ).Comp (fun k => (e k).toX)
      (laU (T.U j σ) (wtA w) w.n) M wg large₂.sc.L hr1 hL1 hM1 hwg (fun k => (hk k).1) (fun k => (hk k).2.1)
      hlogf hlogr hMl hwgl hdE
      (fun k => ⟨(hk k).2.2.1, le_trans (hk k).2.2.2.1 (by nlinarith),
        le_trans (hk k).2.2.2.2.1 (by nlinarith), le_trans (hk k).2.2.2.2.2.1 (by nlinarith)⟩)
      (by rw [← hZ]; exact hcard)
  refine ⟨NN, hne, hP, ?_⟩
  rw [hZ]
  exact hlog

end GlobalTheory.RunIn
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumFieldChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_incF (a : c.F) :
    ((ddBC hle d).eF (incF c c' hle a) : (covCoeff hle d).F) =
      incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (d.eF a) := Subtype.ext rfl

theorem exists_algOver (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] :
    ∃ _ : Algebra c'.F k, AlgOver c c' hle k := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  let φ : c'.F →ₐ[c.F] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom.toAlgebra, fun a => φ.commutes a⟩

theorem thLa_iff (w : (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (k : Type) [CommRing k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k]
    (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (v : k) :
    thLaValAt d.Xo₂ (covCoeff hle d) (nabBC (le_covCoeff hle d) d.nab₂)
        (fun q => (ddBC hle d).eF (incF c c' hle (w q))) La N
        (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P)) y₂ v ↔
      thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (y₂.res (le_covCoeff hle d) h₂) v := by
  have h := GlobalTheory.FieldBC.shortValAt_bc E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.nab₂ n
    (fun q => d.eF (w q)) La 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) k h₂ y₂ v
  have e : (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P) :
      MvPolynomial (LtN Dw n) (covCoeff hle d).F) =
      MvPolynomial.map (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d))
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => eF_incF hle d a)
  rw [map_one] at h
  unfold thLaValAt
  rw [e]
  exact h

theorem isThClsD_ddBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (Vs' : Type) [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (x : Cl → Vs) (x' : Cl → Vs'), (∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k))) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a m, (IsThClsD Xo c' (ddBC hle d) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol) (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) ↔ IsThClsD Xo c d w La Nc gam vol ep io x f) := by
  intro E _ _ _ H Dw l Xo c c' hle n d Cl _ w La Nc gam vol ep Vs _ _ io Vs' _ _ io' x x' hio hδ a m f hf
  have hcoef : ∀ (k : Type) [Field k] [Algebra c.F k] [Algebra c'.F k], AlgOver c c' hle k → ∀ cl,
      algebraMap c'.F k (incF c c' hle vol * ((gam cl : c'.F))⁻¹ * incF c c' hle (ep cl)) =
        algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) := by
    intro k _ _ _ h cl
    rw [← h, map_mul (incF c c' hle), map_mul (incF c c' hle), map_inv₀, map_natCast]
  have hf' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a m f hf).2
  have hδ' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ hδ).2
  have hov := (GlobalTheory.T.levelCover_larger_coeffField_lying_over E H Dw l Xo c c' hle n d).1
  constructor
  · intro H' k _ _ _ _ hk y y₂ hy
    obtain ⟨A, h⟩ := exists_algOver hle k
    letI A₂ : Algebra (covCoeff hle d).F k := A
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun b => by
      obtain ⟨b, rfl⟩ := d.eF.surjective b
      rw [hk, ← h b]
      rfl
    obtain ⟨vc, hv, he⟩ := @H' k _ _ A A₂ (fun _ => rfl) (y.ext hle h) (y₂.ext (le_covCoeff hle d) h₂)
      ((hov k h h₂ _ _).2 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · have := hv cl
      rw [hio] at this
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ _ _).1 this
    · have e1 := hf' k h (y.ext hle h)
      have e2 := hδ' k h₂ (y₂.ext (le_covCoeff hle d) h₂)
      simp only [hcoef k h] at he
      rw [e1] at he
      exact he.trans (congrArg (· * _) e2)
  · intro H' k _ _ A A₂ hk y y₂ hy
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI := resAlg hle k
    letI := resAlg (le_covCoeff hle d) k
    have h : AlgOver c c' hle k := fun _ => rfl
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun _ => rfl
    obtain ⟨vc, hv, he⟩ := H' k (fun b => hk (incF c c' hle b)) (y.res hle h)
      (FrPt.res (c' := covCoeff hle d) (le_covCoeff hle d) h₂ y₂) ((hov k h h₂ y₂ y).1 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · rw [hio]
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ y₂ _).2 (hv cl)
    · have e1 := hf' k h y
      have e2 := hδ' k h₂ y₂
      simp only [hcoef k h]
      rw [e1]
      exact he.trans (congrArg (· * _) e2.symm)

end GlobalTheory.ClassSumFieldChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem thetaRule_value_periods : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (xf : (U.X k).dom) (W : UnfAt U k xf) (Wu : UnitAt W) (nab : NabV Xo c), IsNab Xo c nab → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k xf) → ∀ (n : ℕ) (x x2 : Fin n → Dw.La), (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ b, x2 b - x b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → Differentiable ℂ Wu.θ ∧ toC (evR Xo c f (U.un k xf)) = ((l.M : ℂ)⁻¹) ^ P.totalDegree * I2.polyDeriv (MvPolynomial.map σ P) (letDir W.e) (fun z => ∏ b, fock Wu.Hm ((l.M : ℤ) ^ 2) (((l.M : ℂ) ^ 2)⁻¹ • W.Pm (W.F.t (W.ik k) (x2 b))) (fun w => Wu.θ ((l.M : ℂ) • w)) (z b)) 0 := by
  intro hci E _ _ _ H Dw l Xo c _ σ r U k xf W Wu nab hnab hft n x x2 h2 hx a P hP f hf
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Φ, hof, hHm, -, -, hrd, -, hlin, hlev⟩ := GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame E H Dw l Xo c σ r U k xf W Wu
  have hv := GlobalTheory.T.thetaRuleValue_testRing_eq_thetaValue hci E H Dw l Xo c nab hnab a n x P hP f hf (CAt σ) (U.un k xf) hft
  refine ⟨((GlobalTheory.AnVal.reading_existsUnique_isTh _ _ _ _ _ Φ.toAnFr 1 _).2.1 _ hrd).1, ?_⟩
  have key := GlobalTheory.T.thetaValue_analyticFrame_eq_polyDeriv_fock hci E H Dw l Xo c (U.un k xf) W.g _ W.e Φ
    (W.Pm.comp (W.F.t (W.ik k)).toAddMonoidHom) (fun a => by rw [hof.2.1]; exact ⟨_, rfl⟩) hlin hlev nab hnab Wu.θ hrd
    n x x2 h2 hx a P hP _ hv
  rw [hHm] at key
  exact key

end GlobalTheory.AnVal
end
