module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle196
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMStepA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle044
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

theorem lvlA_last : LvlA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D' Y hz hz' hD J₀ hJ₀ c hc g hg hgD
  have h := Formalism.FourierDecayAlt.P.Qx6.lvlA (E := Wq →L[ℂ] Wp) hz hz' (TemperedBoundGL3.lr hr) (by show r - 1 + 1 = r; omega) hD hJ₀.1
    hJ₀.2.1 hJ₀.2.2.1 Y hc (by rw [TemperedBoundGL3.lr_succ]; exact hg) hgD
  rw [TemperedBoundGL3.lr_succ] at h
  exact h

theorem mirror_residue_first_move : JDRvStepA := jDRvStepA_of_lvlA lvlA_last

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KrAA : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), KB.CptCoef Bs F → ∀ (u : ℂ), ∀ x ∈ B.GV k r,
      PBG.Kr Bs (C3.AAop k r r le_rfl u F) x = C3.AAop k r r le_rfl u (PBG.Kr Bs F) x

section point

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem ptSize_app (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by
  simp [D.ptSize]

theorem smoothOnH_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem pt_poly (hKA : KrAA) (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    (h : C.LPt) (s : ℕ) (t : ℂ) (hs : 2 ≤ s) (hq : D.IsLocPt (h ++ [(s, t)]) (r + 1)) {γ : B.Mat k r}
    (hγ : γ ∈ B.GV k r) (hZγ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (h ++ [(s, t)]) (r + 1))
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    ∃ c : Fin (D.ptSize h + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last _) = ((-1) ^ (s - 1) / t) • PBG.Kr Bs G ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) ∧
      ∀ y : ℝ, PBG.Kr Bs (PBN.aaTop Bs y G) ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) =
        ∑ n : Fin (D.ptSize h + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  set Gσ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => G (σ * g) with hGσdef
  have hGσ : KB.CptCoef Bs Gσ := cpt_left Bs hG hx
  have hp := inSS_pL Bs hx
  have hσS : σ ∈ Sset k r Bs.z :=
    ⟨(Matrix.of x.1 : B.Mat k r)⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hx.1, (Matrix.of x.2 : B.Mat k r)⁻¹,
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hx.2, rfl⟩
  have h1S : (1 : B.Mat k r) ∈ Sset k r Bs.z := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have h1S' : (1 : B.Mat k r) ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have hdσ : ∀ (g : B.Mat k r) (l : Fin (r + 2)), Dmin k r Bs.z Bs.z' (σ * g) l = Dmin k r Bs.z Bs.z' g l := by
    intro g l
    have := Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g l
    rwa [sgs_pL] at this

  have hsz : D.ptSize h + s = r + 1 := by rw [← ptSize_app h s t]; exact hq.2
  have ht : t ≠ 0 := (hq.1 (s, t) (by simp)).2
  set i0 := D.ptSize h with hi0
  set hh := D.ptMatN h i0 with hhh
  have hZ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' γ a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b
    rw [hZγ]
    exact ptMatN_zb h s t (r + 1) hsz.symm a b
  have hDlast : Dmin k r Bs.z Bs.z' γ (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hTT : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
    have : Gf k r Bs.z Bs.z' γ ≤ 0 := by
      unfold Gf
      rw [h0, map_zero]
      nlinarith [Complex.normSq_nonneg (Dmin k r Bs.z Bs.z' γ ⟨r, by omega⟩)]
    linarith
  have hdet : hh.det ≠ 0 := by
    intro h0
    apply hDlast
    rw [dmin_zb Bs.z Bs.z' γ i0 s hh t hZ]
    have := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).2
    rw [show ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = i0 + s by simp; omega, this, h0]
    ring
  have hT' : herm (Hpk k r) Bs.z' Bs.z' ≠ 0 := by
    intro h0
    have := Bs.T'_pos
    unfold Tz at this
    rw [h0] at this
    simp at this
  obtain ⟨n0, hn0, yb, hyb, hzy, hnf1, hnf2⟩ :=
    nf_top Bs.z Bs.z' Bs.z'_mem hT' γ hγ i0 s hs hsz hh hdet t ht hZ
  have hn0N : n0 ∈ Formalism.QuantumDeterminants.Nset k r := stabilizer_mem_unipotent hn0
  have hn0S : n0 ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, n0, hn0N, (Matrix.one_mul n0).symm⟩
  have hx₁G : γ * n0 ∈ B.GV k r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hn0N.1
  have hZ₁ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' (γ * n0) a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]; exact hZ a b
  have hD₁ : ∀ l : Fin (r + 2), Dmin k r Bs.z Bs.z' (γ * n0) l = Dmin k r Bs.z Bs.z' γ l := by
    intro l; unfold Dmin; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]

  set K : B.Mat k r → (Wq →L[ℂ] Wp) := PBG.Kr Bs Gσ with hKdef
  have hKloc := loc_kr Bs hGσ
  have hKn0 : ∀ g, K (g * n0) = K g := by
    intro g
    rw [hKdef, PBG.kr_rightEq Bs Gσ g n0 hn0N, character_stabilizer_eq_one Bs.z'_mem cStd hn0, one_smul]
  have hKσ : ∀ g, K g = PBG.Kr Bs G (σ * g) := fun g => kr_left Bs G σ g
  have hR : ∀ g ∈ Q.Glev k r 0 ∩ Set.univ, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q K g = C3.dpsiP k r Bs.z' p q • K g :=
    fun g _ p q hpq => PBG.kr_rule Bs Gσ g p q hpq
  obtain ⟨c, hc, hcy⟩ := top_poly isOpen_univ Bs.z Bs.z' yb i0 s hs hsz hh t hdet ht (γ * n0)
    ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 _).2 hx₁G, Set.mem_univ _⟩ Bs.z'_mem hyb hzy hnf1 hnf2 hZ₁ K
    (smoothLev_of_loc hKloc) hR
  refine ⟨c, ?_, fun y => ?_⟩
  · rw [hc, hKn0, hKσ]
  · rw [← hcy y, hD₁]
    set u : ℂ := (y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu

    have hX1 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 K Bs.z_mem Bs.z'_mem
      (smoothOnH_of_loc hKloc) 1 h1S n0 hn0S γ hγ).1
    have e1 : (fun g => K (1 * g * n0)) = K := by
      funext g; rw [Matrix.one_mul, hKn0]
    rw [e1, Matrix.one_mul] at hX1
    rw [← hX1]

    have hleft : ∀ g ∈ B.GV k r, PBN.aaTop Bs y G (σ * g) = PBN.aaTop Bs y Gσ g := by
      intro g hg
      unfold PBN.aaTop
      rw [hdσ]
      have hX0 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 G Bs.z_mem Bs.z'_mem
        (smoothOnH_of_ckOn hG.1) σ hσS 1 h1S' g hg).1
      have e2 : (fun x => G (σ * x * 1)) = Gσ := by funext x; rw [Matrix.mul_one]
      rw [e2, Matrix.mul_one] at hX0
      rw [hX0]
    have hKA' := hKA k r Wp Wq Bs Gσ hGσ u γ hγ
    calc PBG.Kr Bs (PBN.aaTop Bs y G) (σ * γ)
        = PBG.Kr Bs (fun g => PBN.aaTop Bs y G (σ * g)) γ := (kr_left Bs _ σ γ).symm
      _ = PBG.Kr Bs (PBN.aaTop Bs y Gσ) γ := kr_congr Bs hleft hγ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • PBG.Kr Bs (C3.AAop k r r le_rfl u Gσ) γ :=
          kr_dmin Bs (C3.AAop k r r le_rfl u Gσ) (Fin.last _) γ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K γ := by rw [hKA']

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rot_alg (ζ D1 DI : ℂ) : -(ζ.im : ℂ) * D1 + (ζ.re : ℂ) * DI =
    Complex.I * (ζ * ((1 / 2 : ℂ) * (D1 + -Complex.I * DI)) - star ζ * ((1 / 2 : ℂ) * (D1 + Complex.I * DI))) := by
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz +
    ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq

theorem rotation_wirtinger_holds : GTRRWirt := by
  intro r u x hu
  have h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
  have h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0 := by
    have h3 := h1.const_mul x.2
    simpa using h3
  have hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r))
      ((0 : Fin r → ℂ), x.2 * Complex.I) 0 := by
    first
    | exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2
    | exact (hasDerivAt_const (0 : ℝ) x.1).prod h2
  have hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r) := by simp
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx
  have hdir1 : MA.dirE (M.vz (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]
  have hdir2 : MA.dirE (M.vzb (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]
  have hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir1]
    simp [M.vz]
  have hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir2]
    simp [M.vzb]
  have key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) =
      fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I) := by
    rw [hw1, hw2, ← rot_alg]
    have hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) +
        (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ)) := by
      refine Prod.ext (by simp) ?_
      simp only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp
    rw [hv, map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hc

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def NFHypL : Prop :=
  ∀ (k r : ℕ) (a : C.LPt) (hle : D.ptSize a ≤ r) (g' : B.Mat k (r - D.ptSize a)), g' ∈ B.GV k (r - D.ptSize a) →
    D.IsLocPt a (D.ptSize a) →
    levelZeroPointOver a hle g' ∈ B.GV k r ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.xi0 (levelZeroPointOver a hle g') a' q =
        if hq : q.val < D.ptSize a then U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0) ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.y0 (levelZeroPointOver a hle g') a' q =
        if hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a then
          star (U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0)

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (i j : Fin (2 * b + k + 1)) :
    D.castM h g i j = g (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := rfl

theorem embedding_map_apply_last_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (c : Fin p)
    (j : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ (U.eB k p ρ (Sum.inr c)) j =
      if hj : j.val < p then Z c.rev ⟨j.val, hj⟩ else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_left (by rw [Ux3.block_index_first_val]; exact y.isLt)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [Ux3.wMat_mul_apply]
    exact congrArg (Z c.rev) (Fin.ext (Ux3.block_index_first_val (k := k) (ρ := ρ) y).symm)
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr]
  · rw [dite_eq_right (by rw [Ux3.block_index_last_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₂]

theorem embedding_map_apply_first_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (b : Fin p)
    (i : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ i (U.eB k p ρ (Sum.inl (Sum.inl b))) =
      if hi : p + (2 * ρ + k + 1) ≤ i.val then
        (G.wMat p * Z) ⟨i.val - (p + (2 * ρ + k + 1)), by omega⟩ b else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective i
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_right (by rw [Ux3.block_index_first_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_left (by rw [Ux3.block_index_last_val]; omega)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    exact congrArg (fun c => (G.wMat p * Z) c b) (Fin.ext (by
      show (U.eB k p ρ (Sum.inr y)).val - (p + (2 * ρ + k + 1)) = y.val
      rw [Ux3.block_index_last_val]; omega)).symm

theorem normal_form_left_hypothesis : NFHypL := by
  intro k r a hle g' hg' hloc
  have hd : ∀ i, D.ptDiag a i ≠ 0 := fun i => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hloc.1 i i.2
  have hZ : (U.hMat (D.ptPerm a) (D.ptDiag a)).det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd
  have hM : U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g' ∈
      B.GV k (D.ptSize a + (r - D.ptSize a)) :=
    (Formalism.FourierDecayAlt.P.slice_membership k (D.ptSize a) (r - D.ptSize a)).1 _ g' hZ hg'
  refine ⟨Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM, fun a' q ha' => ?_, fun a' q ha' => ?_⟩
  · unfold PBG.xi0
    rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    unfold levelZeroPointOver
    rw [castM_apply']
    have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inr ⟨D.ptSize a - 1 - a'.val, by omega⟩) := by
      ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
    rw [hi, embedding_map_apply_last_block]
    by_cases hq : q.val < D.ptSize a
    · rw [dite_eq_left (by simpa using hq), dite_eq_left hq]
      congr 1; ext; simp [Fin.val_rev]; omega
    · rw [dite_eq_right (by simpa using hq), dite_eq_right hq]
  · unfold PBG.y0
    rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    have hgu : IsUnit g'.det := WeylGroupFacts.isUnit_of_uh hg'
    unfold levelZeroPointOver
    rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZ) hgu, castM_apply']
    have hj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
      ext; rw [Ux3.block_index_first_val]; simp [eI]
    rw [hj, embedding_map_apply_first_block]
    by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a
    · rw [dite_eq_left (by simp; omega), dite_eq_left hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
      congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
    · rw [dite_eq_right (by simp; omega), dite_eq_right hq]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section

open Filter Topology

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem limit_of_module_forms : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := PBE.belowTop
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end Formalism.FourierDecayAlt.P
end
