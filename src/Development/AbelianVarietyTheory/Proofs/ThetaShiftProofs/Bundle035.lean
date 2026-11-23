module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDB
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by

  rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)

    rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (AddMonoidAlgebra.coeff · μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  change (∑ i, (MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))).coeff μ) = 0 at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace GlobalTheory.ArcQ

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : S →ₐ[c.F] S ⧸ P := Ideal.Quotient.mkₐ c.F P
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (S ⧸ P)ˣ := fun i => Units.map (φ : S →* S ⧸ P) (t i)
  have hb : FrBor t' z z' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (S ⧸ P)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := evR_frBor_of_isDomain hL hF t' z z' hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change φ _ = 0
  rw [map_sub, hw, map_mul, sub_eq_zero]
  congr 1
  simp [wchar, t']

theorem evR_scale_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {A T : Type} [CommRing A] [Algebra c.F A] [IsReduced A]
    [CommRing T] [Algebra c.F T] (φ : A →ₐ[c.F] T) (g : Tˣ) (y : FrPt Xo c A) (z z' : FrPt Xo c T)
    (hm : FrMap φ y z) (hb : FrBor (fun i => i.elim g fun _ => 1) z z') :
    evR Xo c F z' = (g : T) ^ n * φ (evR Xo c F y) := by
  classical
  obtain ⟨G, hG1, hG2, hG⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c T).2.2.2 _ z z').1 hb
  let ι := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ))
  let R := MvPolynomial ι A
  let B := Localization.Away (MvPolynomial.X none : R)
  let v : ι → T := fun i => i.elim (g : T) fun x => G x.1 x.2.1 x.2.2
  let k₀ : R →ₐ[c.F] T := MvPolynomial.aevalTower φ v
  have hk₀ : IsUnit (k₀ (MvPolynomial.X none)) := by simp [k₀, v, R]
  let k : B →ₐ[c.F] T := IsLocalization.liftAlgHom (M := Submonoid.powers (MvPolynomial.X none : R)) (f := k₀)
    (by rintro ⟨_, m, rfl⟩; simpa only [map_pow] using hk₀.pow m)
  have hk : ∀ r : R, k (algebraMap R B r) = k₀ r := fun r => IsLocalization.lift_eq _ r
  let π : A →ₐ[c.F] B := IsScalarTower.toAlgHom c.F A B
  have hπ : k.comp π = φ := by
    ext x
    change k (algebraMap A B x) = φ x
    rw [IsScalarTower.algebraMap_apply A R B, hk]
    simp [k₀, R]
  have hu : IsUnit (algebraMap R B (MvPolynomial.X none)) := IsLocalization.Away.algebraMap_isUnit _
  let M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B := fun τ => Matrix.of fun i j =>
    if i = j then 1 else if i < j then 0 else algebraMap R B (MvPolynomial.X (some ⟨τ, i, j⟩))
  have hM1 : ∀ τ i, M τ i i = 1 := fun τ i => by simp [M]
  have hM2 : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by simp [M, hij, hij.ne]
  have hMk : ∀ τ, (M τ).map k = G τ := fun τ => by
    ext i j
    by_cases h1 : i = j
    · subst h1; simp [hM1, hG1]
    · by_cases h2 : i < j
      · simp [hM2 τ i j h2, hG2 τ i j h2]
      · simp only [M, Matrix.map_apply, Matrix.of_apply, if_neg h1, if_neg h2, hk]
        simp [k₀, v, R]
  have hdet : ∀ τ, IsUnit (M τ).det := fun τ => by
    rw [Matrix.det_of_isLowerTriangular (M τ) (fun i j hij => hM2 τ i j hij)]
    simp [hM1]
  obtain ⟨u₀, hu₀⟩ := hL.bc _ _ π y
  obtain ⟨u, hchg⟩ := (GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c B M _ u₀).1 hdet hu
  have h0 : FrMap k u₀ z := frMap_cancel (Xo := Xo) (c := c) _ _ _ π k y u₀ z hu₀ (by rw [hπ]; exact hm)
  have h1 : FrMap k u z' := by
    refine ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.1 _ k M _ u₀ u z z' hchg h0).2 ?_
    have e : k (algebraMap R B (MvPolynomial.X none)) = (g : T) := by rw [hk]; simp [k₀, v, R]
    rw [e, show (fun τ => (M τ).map k) = G from funext hMk]
    exact hG
  let t : Ix Dw → Bˣ := fun i => i.elim hu.unit fun _ => 1
  have hbu : FrBor t u₀ u :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.2 t u₀ u).2 ⟨M, fun τ i => by simp [t, hM1], hM2, hchg⟩
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF B _ k u z' h1,
    evR_frBor_of_isReduced hL hF t u₀ u hbu,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF A _ π y u₀ hu₀, map_mul, ← hπ]
  congr 1
  have e : wchar (ex Dw a n) t = algebraMap R B (MvPolynomial.X none) ^ n := by
    simp [wchar, t, ex, Fintype.prod_option]
  rw [e, map_pow, hk]
  simp [k₀, v, R]

end General

end GlobalTheory.ArcQ
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

theorem assemble (K M P z s lc lL lr lR lo ld ln : ℝ) (hz : 1 ≤ z) (hP : z ≤ P) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hs : 1 ≤ s) (hc : lc ≤ K * z) (hL : lL ≤ M * P) (hr : lr ≤ K * z) (hR : lR ≤ z) (ho : lo ≤ K * z)
    (hd : ld ≤ K * z) (hn : ln ≤ M * P) :
    4 * Real.pi + (lc / 2 + lL + lr + lR) * s ≤ (17 + 2 * K + M) * P * s ∧
    ((1 + lo) / 2 + (1 / 2) * lL) * s ≤ (17 + 2 * K + M) * P * s ∧
    ld + ln ≤ (17 + 2 * K + M) * P := by
  have hKz : K * z ≤ K * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hKP : 0 ≤ K * P := by nlinarith
  have hMP : 0 ≤ M * P := mul_nonneg hM (by linarith)
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)
    have h3 : 1 ≤ P * s := by nlinarith
    nlinarith
  · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · nlinarith

theorem log_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := Real.log_le_self hx

end GlobalTheory.ArcCM.Room
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFrame

theorem valR_g_self {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (x : Sp A ⟶ Z)
    (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  have toStkA_valR {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
      toStkA z (valR x U a.val) = (gm x z U a).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
      ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem valR_rig {A A₀ : Type} [CommRing A] [IsLocalRing A] [CommRing A₀] {B : Over (Sp A)} {B₀ : Over (Sp A₀)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₀] [IsCommMonObj B₀] {M : LB B.left} {M₀ : LB B₀.left} (f : A₀ →+* A)
    {φ : B.left ⟶ B₀.left} (he : eSec B ≫ φ = spMap f ≫ eSec B₀) (w : LB.Iso M (M₀.pull φ))
    (r : LB.Gen (M.pull (eSec B))) (r₀ : LB.Gen (M₀.pull (eSec B₀)))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec B) (fun _ => 1)) r (rigPullOf φ (spMap f) he M₀ r₀))
    (j : M.ι) (j₀ : M₀.ι) (hj : ⊤ ≤ (show Sp A ⟶ _ from eSec B) ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀, j))
    (hj₀ : ⊤ ≤ (M₀.pull (eSec B₀)).U (fun _ => j₀)) :
    f (valR (𝟙 (Sp A₀)) ((M₀.pull (eSec B₀)).U (fun _ => j₀)) (r₀.s (fun _ => j₀)).val) =
      valR (A := A) (eSec B) _ (w.s (fun _ => j₀, j)).val *
        valR (𝟙 (Sp A)) ((M.pull (eSec B)).U (fun _ => j)) (r.s (fun _ => j)).val := by
  have hc := hj (show cpt A ∈ (⊤ : (Sp A).Opens) from trivial)
  have e := gm_maps_pt h (𝟙 (Sp A)) (cpt A) (fun _ => j₀) j hc.1 hc.2
  have hr : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ (M.pull (eSec B)).U (fun _ => j) := fun z hz => mem_pull.2 (hj hz).2
  have h₀ : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ (M₀.pull (eSec B₀)).U (fun _ => j₀) := hj₀
  have h₁ := FormalValue.top_le_comp h₀ (spMap f)
  apply toStkA_injective
  refine Eq.trans ?_ ((congrArg Units.val e).trans ?_)
  · refine (congrArg _ (FormalValue.valR_spMap f _ _ h₀ _).symm).trans ((toStkA_valR _ _ _ h₁ _).trans
      (congrArg Units.val ?_))
    have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ ((M₀.pull φ).pull (eSec B)).U (fun _ _ => j₀) := mem_pull.2 hc.1
    refine Eq.trans ?_ ((gm_res (𝟙 (Sp A)) _ _ hm _).trans (gm_pull (𝟙 (Sp A)) (spMap f) _ _ (hj₀ trivial) _)).symm
    rw [Category.id_comp, Category.comp_id]
  · refine Eq.trans ?_ (map_mul _ _ _).symm
    exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) (toStkA_valR (A := A) (eSec B) _ _ hj _).symm
      (toStkA_valR _ _ _ hr _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : _root_.GlobalTheory.ArcPts.GtAn a}
  (Ξ : ConstPts W Λ)


omit [Algebra (FractionRing ℂ) ℂ] in
theorem complete : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
  rw [Algebra.algebraMap_self, Ideal.map_id]
  infer_instance

theorem base_comp (v : Λ.A.V) :
    (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
  ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) (base_comp Ξ v)).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isFrm (v : Λ.A.V) : IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v) := by
  haveI := complete
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g v) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  refine ⟨fun j h => ?_, fun j j' h => ?_⟩
  · refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM j₀ h hj)).mpr ?_)
    exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)
  · have h₁ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j := fun z hz => (h hz).1
    have h₂ : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j' := fun z hz => (h hz).2
    have t := FormalValue.tau_trans (Ξ.x_fm v) h₁ h₂ hM hM
    rw [valR_g_self W.P.D.toPre.P.isLB _ jM hM, _root_.mul_one] at t
    have e₁ := Ξ.τ_eq v j jM j₀ h₁ hj
    have e₂ := Ξ.τ_eq v j' jM j₀ h₂ hj
    refine hw.mul_left_cancel (e₁.trans ?_)
    refine (congrArg (· * _) t).trans ?_
    rw [_root_.mul_assoc, mul_left_comm]
    exact (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans (mul_left_comm _ _ _))

theorem tau_zero (hx : Ξ.x 0 = 1) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j))
      (W.P.U.LG.rig.s (fun _ => j)).val := by
  haveI := complete
  have hs : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ 0
  have hw := FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g 0).b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hM : ⊤ ≤ FormalValue.basePt (Ξ.g 0) ⁻¹ᵁ W.P.D.toPre.P.L.U jM := fun z hz => (hj hz).2
  have hx' : (Ξ.x 0).left = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G := by
    refine (congrArg Over.Hom.left hx).trans ?_
    exact congrArg (· ≫ eSec W.t.G) ((Category.comp_id _).symm.trans (Over.w (toUnit selfR)))
  have hu : (Λ.u.ex (0 : Λ.A.V).2).left = eSec a.D₀.P.A := by
    refine (congrArg Over.Hom.left ((Λ.u.ker 0).2 Λ.u.Λ.zero_mem)).trans ?_
    rw [Hom.one_def]; simp [eSec]
  have hb : FormalValue.basePt (Ξ.g 0) = eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · exact (base_comp Ξ 0).trans ((congrArg (_ ≫ ·) hu).trans W.he.symm)
    · exact (Over.w (Ξ.g 0).b).trans (hs.trans (Over.w η[W.P.D.toPre.P.A]).symm)
  have hb' : FormalValue.basePt (Ξ.g 0) = spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.P.D.toPre.P.A :=
    hb.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hs.symm))
  have hf := Ξ.x_fm 0
  have e := Ξ.τ_eq 0 j jM j₀ h hj
  rw [hx'] at hf h e
  have t := FormalValue.tau_rig hf hb' h hM
  have hj₀ : ⊤ ≤ (a.D₀.P.L.pull (eSec a.D₀.P.A)).U (fun _ => j₀) := fun z hz =>
    mem_pull.2 ((congrArg (fun q => q z ∈ a.D₀.P.L.U j₀) hu).mp (h₀ hz))
  have r := valR_rig (PowerSeries.C (R := ℂ)) W.he W.w W.P.D.toPre.rig a.D₀.rig W.spec.2.2.1 jM j₀ (hb ▸ hj) hj₀
  have f := (congrArg (PowerSeries.C (R := ℂ)) (Λ.rig (fun _ => j₀) hj₀)).trans r
  replace f := f.trans (congrArg (fun q => valR (A := ℂ⟦X⟧) q _ (W.w.s (fun _ => j₀, jM)).val * _) hb.symm)
  refine hw.mul_left_cancel (e.trans ((congrArg (_ * ·) f).trans ((mul_left_comm _ _ _).trans (congrArg (_ * ·) ?_))))
  have t' := t
  generalize FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec W.t.G) j jM = q at t' ⊢
  rw [hs] at t'
  exact t'


omit [Algebra (FractionRing ℂ) ℂ] in
theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) , (∀ v, IsFrm W.P.U.LG.L (Ξ.x v).left (Ξ.τ v)) ∧ ∀ j, ⊤ ≤ (Ξ.x 0).left ⁻¹ᵁ W.P.U.LG.L.U j → Ξ.τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((W.P.U.LG.L.pull (eSec W.t.G)).U (fun _ => j)) (W.P.U.LG.rig.s (fun _ => j)).val := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ
  refine ⟨isFrm Ξ, tau_zero Ξ ?_⟩
  have h := (GlobalTheory.ArcPts.constPts_add_smul h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ).1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

end GlobalTheory.ConstFrame
end
end
