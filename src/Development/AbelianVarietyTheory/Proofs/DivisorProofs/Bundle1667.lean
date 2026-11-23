module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leadMinor_re_pos_of_posDef {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) :
    0 < (leadMinor G j).re := by
  have hsub : (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).PosDef :=
    hG.submatrix Subtype.val_injective
  have h := hsub.det_pos
  unfold leadMinor
  exact (Complex.pos_iff.mp h).1

theorem contDiffAt_leadMinor {n s : ℕ} {G : V n → Matrix (Fin s) (Fin s) ℂ} {v : V n}
    (h : MContDiffAt ∞ G v) (j : ℕ) : ContDiffAt ℝ ∞ (fun x => leadMinor (G x) j) v :=
  (h.submatrix _ _).det

theorem ldPart_grD_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef →
    MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  intro n s G v hG hp
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hnum : ContDiffAt ℝ ∞ (fun x => ((G x).submatrix
        (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det) v :=
      (hG.submatrix _ _).det
    have hden := contDiffAt_leadMinor hG (j : ℕ)
    have hne : leadMinor (G v) j ≠ 0 := fun h0 => by
      have := leadMinor_re_pos_of_posDef hp j
      rw [h0] at this; simp at this
    simp only [ldPart, Matrix.of_apply]
    exact hnum.mul (hden.inv hne)
  · have hnum : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) (i + 1)).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    have hden : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) i).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    exact hnum.div hden (leadMinor_re_pos_of_posDef hp i).ne'

end GlobalTheory.ChernCalc
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.CurvSmooth

theorem curvEv_entry_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, (∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b)) ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) v) := by
  intro n r _ _ G v hG hu i j
  have e : ∀ x, (curvEv G x i j : Alt n) = ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    intro x

    simp [curvEv, curvPoly, Matrix.map_apply, map_sum, sym, Algebra.smul_def]
  refine ⟨e, fun S => ?_⟩
  have hc : ∀ a b, ContDiffAt ℝ ∞ (fun x => curv G x (coordVec a) (coordVec b) i j) v := fun a b =>
    MContDiffAt.curv (j := ∞) hG hu (le_of_eq rfl) _ _ i j
  have hf : (fun x => (bas n).repr ((curvEv G x i j : Alt n)) S) =
      fun x => ∑ a, ∑ b, curv G x (coordVec a) (coordVec b) i j * (bas n).repr (dz a * dzb b) S := by
    funext x
    rw [e x]

    simp [map_sum, Finsupp.finsetSum_apply]
  rw [hf]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (hc a b).mul contDiffAt_const

end GlobalTheory.CurvSmooth
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.TopPow

open ReciprocityTheory.L2DbarEstimates (cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, GlobalTheory.CxForm.DensPow.dens_pow, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {L : LB X.X}

theorem dens_loc_c1W_pow (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    (y : CxPts X.str σ) (hy : y ∈ c.e.source) :
    (dens ((atlas X σ).loc (fld (atlas X σ) (c1W ψ ^ X.dim)) c (c.e y))).re = c.chernDens ψ y := by
  have e := (atlas X σ).loc_crd (fld (atlas X σ) (c1W ψ ^ X.dim)) (⟨(c, y), hy⟩ : (atlas X σ).Pt)
  erw [e]
  have hs := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  erw [fld, Pi.pow_apply, c1W, dens_ofValues_ddc_pow X.dim _ _ hs]
  rfl

theorem part_c1W_pow : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L),
    ψ.IsCInf → ∀ ε : ℤˣ, (atlas X σ).part (fld (atlas X σ) (c1W ψ ^ X.dim)) ε = ψ.chernPart X.dim ε := by
  intro F _ σ X L ψ hψ ε
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_c1W_pow ψ hψ c _ hy]

end GlobalTheory.ChernCalc.TopPow
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.FrameInv

section Algebra

variable {r R : Type} [Fintype r] [DecidableEq r] [CommRing R] {P Q : Matrix r r R}

theorem conj_pow (h : Q * P = 1) (A : Matrix r r R) (k : ℕ) : (P * A * Q) ^ k = P * A ^ k * Q := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h, one_mul]

theorem trace_conj' (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, h, one_mul]

theorem charpolyRev_conj (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).charpolyRev = A.charpolyRev := by
  have h' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 - (Polynomial.X : Polynomial R) • (P * A * Q).map Polynomial.C : Matrix r r (Polynomial R)) =
      P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • A.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 h', Matrix.mul_smul,
      Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    mul_eq_one_comm.1 h', Matrix.det_one, one_mul]

theorem conj_mul_three (h : Q * P = 1) (A B C : Matrix r r R) :
    (P * A * Q) * (P * B * Q) * (P * C * Q) = P * (A * B * C) * Q := by
  simp only [mul_assoc]
  rw [← mul_assoc Q P, h, one_mul, ← mul_assoc Q P, h, one_mul]

end Algebra

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem curvPoly_eq_sum (G : V n → Matrix r r ℂ) (v : V n) : curvPoly G v =
    ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext1 i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem curvPoly_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) : curvPoly G₂ v = P.map C * curvPoly G v * Q.map C := by
  simp only [curvPoly_eq_sum, h, Matrix.map_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem curvEv_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) :
    curvEv G₂ v = P.map (algebraMap ℂ (Ev n)) * curvEv G v * Q.map (algebraMap ℂ (Ev n)) := by
  have e (M : Matrix r r ℂ) : (M.map C).map (aeval (R := ℂ) (sym (n := n))) = M.map (algebraMap ℂ (Ev n)) := by
    ext1 i j
    simp only [Matrix.map_apply, aeval_C]
  rw [curvEv, curvPoly_conj h, Matrix.map_mul, Matrix.map_mul, e, e, curvEv]

theorem pow_chern_trans_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  intro n r _ _ G G' G₂ G₂' T K K' v hG uG hG' uG' hT uT hK uK hK' uK' h k
  obtain ⟨c₁, f₁⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G G₂ T K v hG uG hT uT hK uK (h.mono fun _ hx => hx.1)
  obtain ⟨c₂, f₂⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G' G₂' T K' v hG' uG' hT uT hK' uK' (h.mono fun _ hx => hx.2)
  have u : (T v)ᵀ * (T v)ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have uE : (T v)ᵀ.map (algebraMap ℂ (Ev n)) * (T v)ᵀ⁻¹.map (algebraMap ℂ (Ev n)) = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  have uC : (T v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * (T v)ᵀ⁻¹.map C = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [powAt, curvEv_conj f₁, conj_pow uE, trace_conj' uE, powAt]
  · rw [chernAt, chernPoly, curvPoly_conj f₁, ← neg_mul, ← mul_neg, charpolyRev_conj uC, chernAt, chernPoly]
  · have c (ξ : V n) : conn G₂ v ξ - conn G₂' v ξ = (T v)ᵀ⁻¹ * (conn G v ξ - conn G' v ξ) * (T v)ᵀ := by
      rw [c₁, c₂, ← mul_sub, add_sub_add_right_eq_sub, ← sub_mul, mul_assoc]
    unfold transAt
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [c, curvEv_conj f₁, curvEv_conj f₂, conj_pow uE, conj_pow uE, Matrix.map_mul, Matrix.map_mul,
      conj_mul_three uE, trace_conj' uE]

end GlobalTheory.ChernCalc.FrameInv
end
end

section

set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.ChernCalc.CurvClosed

theorem dbar_dbar_comm {n : ℕ} {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x w) z v = dbar (fun x => dbar u x v) z w := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key (a b : V n) : dbar (fun x => dbar u x b) z a = (1 / 2 : ℂ) • (dbar (fun x => fderiv ℝ u x b) z a +
      Complex.I • dbar (fun x => fderiv ℝ u x (Complex.I • b)) z a) := by
    rw [show (fun x => dbar u x b) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x b + Complex.I • fderiv ℝ u x (Complex.I • b))
      from rfl, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) v, hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem sum_symm {n : ℕ} {s : Fin n → Fin n → Fin n → ℂ} (hs : ∀ a c b, s a c b = s a b c) :
    ∑ c, ∑ p : Fin n × Fin n, s p.1 c p.2 • (dzb c * (-(dz p.1 * dzb p.2)) : Alt n) = 0 := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  have h := congrArg (dz a * ·) (PullClosed.sum_symm_dzb (hs a))
  simp only [Finset.mul_sum, mul_smul_comm, mul_zero] at h
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_) h
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← neg_mul, dz, dzb,
    ← eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)]

theorem curvEv_apply {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (x : V n) (i j : r) :
    (curvEv G x i j : Alt n) = ∑ p : Fin n × Fin n,
      dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2) • (-(dz p.1 * dzb p.2)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, ← Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym,
    Fintype.sum_prod_type, curv, Matrix.neg_apply, mdbar_apply, neg_smul, smul_neg, NegMemClass.coe_neg]

theorem dbarAt_curvEv : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n),
    MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => (curvEv G x i j : Alt n)) v = 0 := by
  intro n r _ _ G v hG hu i j
  have hθ (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn G x (coordVec a) i j) v :=
    hG.conn hu (j := 2) (WithTop.coe_le_coe.2 (le_top : (2 + 1 : ℕ∞) ≤ ⊤)) (coordVec a) i j
  rw [funext fun x => curvEv_apply G x i j,
    PullClosed.dbarAt_sum_smul (ι := Fin n × Fin n)
      (f := fun p x => dbar (fun y => conn G y (coordVec p.1) i j) x (coordVec p.2)) _
      fun p => differentiableAt_dbar_apply (hθ p.1) _]
  exact sum_symm
    (s := fun a c b => dbar (fun x => dbar (fun y => conn G y (coordVec a) i j) x (coordVec b)) v (coordVec c))
    fun a c b => dbar_dbar_comm (hθ a) _ _

end GlobalTheory.ChernCalc.CurvClosed
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem holUnitAt_ratVal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn)
    (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ →
    HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  intro F _ σ X s T y hT hd hdi
  refine ⟨?_, fun c hc a b => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    let T' : Matrix (Fin s) (Fin s) ((ratOf X).O (under y)).toSubring :=
      Matrix.of fun i j => ⟨T i j, mem_O_ratOf.2 (hT i j)⟩
    have e1 : T.map (ratVal · y) = T'.map ψ := by
      ext i j
      exact hψ (T' i j)
    have e2 : ((T'.det : ((ratOf X).O (under y)).toSubring) : X.Fn) = T.det :=
      (RingHom.map_det (((ratOf X).O (under y)).toSubring.subtype) T').trans rfl
    have hu : UnitAt (under y) T.det := (unitAt_iff hd).2 ⟨e2 ▸ mem_O_ratOf.1 T'.det.2, hdi⟩
    have hne := ratVal_ne_zero (y := y) hu
    rw [← e2, hψ] at hne
    show IsUnit (T.map (ratVal · y)).det
    rw [e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 hne
  · obtain ⟨U, hU, g, e⟩ := (hT a b).exists_fnOf
    have hyU : y ∈ ptsIn X.str σ U := mem_ptsIn.2 hU
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hyU)] with v hv
    have hdv : DifferentiableAt ℂ (ev X.str σ U g ∘ c.e.symm) v :=
      (c.holo U g).differentiableAt ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv)
    refine hdv.congr_of_eventuallyEq ?_
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv] with u hu
    show ratVal (T a b) (c.e.symm u) = ev X.str σ U g (c.e.symm u)
    rw [← e, ratVal_fnOf hu.2]

end GlobalTheory.ChernCalc
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

section Pull

variable {F : Type} [Field F] {σ : F →+* ℂ} {X Y : Var F}

theorem ratVal_eq_val_ratOf (y : CxPts X.str σ) {x : X.Fn} (hx : x ∈ (ratOf X).O (under y)) :
    ratVal x y = (ratOf X).val y.1 x := by
  obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 hx).exists_fnOf
  rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
  refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
  rintro _ ⟨w, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]

theorem under_ptMap (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) :
    under (ptMap σ f hf z) = f (under z) := rfl

theorem ratVal_pull {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hφ : (ratOf X).IsHom (ratOf Y) φ f)
    (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) {g : X.Fn} (hg : g ∈ (ratOf X).O (f (under z))) :
    ratVal (φ g) z = ratVal g (ptMap σ f hf z) := by
  rw [ratVal_eq_val_ratOf z (hφ.map_mem_O hg), ratVal_eq_val_ratOf (ptMap σ f hf z) hg]
  exact (hφ.val_comp z.1 _ hg).symm

end Pull

theorem pullGram_eq_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  intro F _ σ X Y ι m E E' φ f hf hR H hH z
  refine ⟨under_ptMap f hf z, ?_⟩
  intro A hA B hB τ
  have hA' : A ∈ E.S (under (ptMap σ f hf z)) := hA
  have hA₀ : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (f (under z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have hA₀' : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (under (ptMap σ f hf z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have htr := hH.trans (ptMap σ f hf z) mem_ptsIn_top A hA' _ hA₀' τ
  unfold pullGram
  rw [htr]
  generalize (E.nonempty (under (ptMap σ f hf z))).choose = A₀ at hA₀ hA₀'

  have hg : Par 0 ((ratOf Y).O (under z)).toSubring (B * (A₀.map φ)⁻¹) := hR.sub (under z) B hB A₀ hA₀
  have hc : Par 0 ((ratOf X).O (f (under z))).toSubring (A₀ * A⁻¹) := (Fr.mem_iff hA).1 hA₀
  have hh : Par 0 ((ratOf Y).O (under z)).toSubring ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)) :=
    hc.map (φ : X.Fn →+* Y.Fn) fun x hx => hR.hom.map_mem_O hx
  have hprod : B * (A₀.map φ)⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map φ)⁻¹ := by
    change B * (A₀.map (φ : X.Fn →+* Y.Fn))⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map (φ : X.Fn →+* Y.Fn))⁻¹
    rw [Mat.map_mul, ← Mat.map_inv, mul_assoc, ← mul_assoc (A₀⁻¹.map _), ← Mat.map_mul,
      Mat.inv_mul (Fr.det_ne hA₀), Mat.map_one, one_mul, Mat.map_inv]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have hmul := hg.map_mul_of hh (ratVal · z) ψ hψ
  rw [hprod] at hmul
  have hval : ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)).map (ratVal · z) = (A₀ * A⁻¹).map (ratVal · (ptMap σ f hf z)) := by
    funext τ'
    ext i j
    exact ratVal_pull hR.hom hf z ((hc τ').1 i j)
  rw [hval] at hmul
  rw [hmul, Pi.mul_apply, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isVacuum_conj_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ), IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  first | exact @GlobalTheory.VacConj.isVacO_conj_negSp | exact GlobalTheory.VacConj.isVacO_conj_negSp | (intros; apply GlobalTheory.VacConj.isVacO_conj_negSp <;> assumption)
end
