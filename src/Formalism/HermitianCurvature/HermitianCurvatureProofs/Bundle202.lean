module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle180
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle193
import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle194
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def hsLE {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp') :
    (Wq' →L[ℂ] Wp') →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq') => Wp') :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => B.hsVec (Eρ.comp X)
      map_add' := fun X Y => by rw [ContinuousLinearMap.comp_add]; unfold B.hsVec; rfl
      map_smul' := fun c X => by rw [ContinuousLinearMap.comp_smul]; exact PBL.hsVec_smul c _ }

theorem hsLE_apply {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] (Eρ : Wp' →L[ℂ] Wp')
    (X : Wq' →L[ℂ] Wp') : hsLE Eρ X = B.hsVec (Eρ.comp X) := rfl

theorem vecV_nonloc {P : M.Par} {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Bs : B.RealPlaceData P.k P.r Wp' Wq')
    (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (Q : C.LPt)
    (hQ : ¬ D.IsLocPt Q (P.r + 1)) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dite_eq_right (fun h => hQ h.1)]

theorem gN_top_gram {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (a : List C.Letter)
    (ha : D.AdmAt S v a) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : I → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] PBL.HV S v),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef (p v).T.base (Fi i)) ∧
      ∀ P Q : C.LPt, KB.gN (PBL.setC S p F) v ε (S.G.r + 1) a P Q =
        ∑ i, (c i : ℂ) * ⟪(omN S a.length Q : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S Q)),
          (omN S a.length P : ℂ) • L i ((p v).V (Fi i) (PBL.stdS S P))⟫_ℂ := by
  classical
  have hgpos := PBL.g_pos_of_built hB
  have hTT := (PBL.pdG_of_built hB v).2
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGr, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hcutw : KB.CutWord (D.parOf S v) (p v).l0 a := by
    obtain ⟨w, hw⟩ := ha
    rw [hl0, ← hw]
    exact PBD.cutWord_of_adm S hGr (PBCut.cutInside_of_built hB) w v
  have hInD' : KB.InDDplus2 (D.parOf S v) (p v).l0 (p v).T.base Cb (p v).Θ := by rw [hl0]; exact hInD
  have hTh : ∀ e : Wd.Ix (Fin a.length), ∃ F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      KB.CptCoef (p v).T.base F' ∧ ∀ Q, (p v).V ((p v).Θ.Θ a e (F v ε)) Q = (p v).V F' Q := by
    intro e
    obtain ⟨F', hF', -, hV⟩ := Formalism.FourierDecayAlt.P.theta_compact_support _ _ (D.parOf S v) (p v) (F v ε) a e Cb hInD'
      (hF v ε hε) hcutw
    exact ⟨F', hF', hV⟩
  choose Fe hFe hVe using hTh
  have hΓ : PBL.ΓS S (S.G.r + 1) = 1 := by simp [PBL.ΓS, D.GamLev]
  refine ⟨Wd.Ix (Fin a.length) × M.Ty (D.parOf S v), inferInstance,
    fun i => PBL.del2 S p v a i.1 i.2 / (PBL.ΓS S (S.G.r + 1) * S.sizeAt v a), fun i => Fe i.1,
    fun i => hsLE ((p v).TP.E i.2), fun i => ?_, fun i => hFe i.1, fun P Q => ?_⟩
  · rw [hΓ, one_mul]
    exact div_nonneg (PBL.second_defect_nonneg S p v a i.1 i.2) (PBL.sizeAt_nonneg S v a)
  by_cases hloc : D.IsLocPt P (S.G.r + 1) ∧ D.IsLocPt Q (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    have hPs : D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [PBL.gN_setC hB, PBL.rr_top_eq Formalism.FourierDecayAlt.P.vector_valued_types (p v) (F v ε) a _ _ hPs hQs]
    unfold Top.topOf
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    dsimp only
    have e1 := hVe e (PBL.stdS S P)
    have e2 := hVe e (PBL.stdS S Q)
    unfold KB.Pl.V at e1 e2
    rw [e1, e2, inner_smul_left, inner_smul_right, hsLE_apply, hsLE_apply]
    have hin : ⟪B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S Q))),
        B.hsVec (((p v).TP.E ρ).comp ((p v).V (Fe e) (PBL.stdS S P)))⟫_ℂ =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S P)))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ (Fe e) (PBL.stdS S Q))) := rfl
    rw [hin]
    set TT := Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (p v).T.base.z' with hTTdef
    by_cases h1 : 0 < D.ptG TT S.G.r (PBL.stdS S P)
    · by_cases h2 : 0 < D.ptG TT S.G.r (PBL.stdS S Q)
      · have hw1 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h1.le) _
        have hw2 : 0 ≤ Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length :=
          pow_nonneg (div_nonneg (Complex.normSq_nonneg _) h2.le) _
        have hd1 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S P) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S P) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw1 _
        have hd2 : Top.dH (D.parOf S v) (p v).l0 TT a (PBL.stdS S Q) e ρ =
            √(Top.wPt TT S.G.r (PBL.stdS S Q) ^ a.length) * √((Top.cW (D.parOf S v) (p v).l0 a e ρ).re) := by
          unfold Top.dH; exact Real.sqrt_mul hw2 _
        rw [hd1, hd2]
        unfold omN PBL.del2
        rw [← hTT]
        simp only [Complex.conj_ofReal]
        push_cast
        ring
      · rw [PBL.vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, PBL.hsInner_zero_right']
        simp
    · rw [PBL.vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, PBD.hsInner_zero_left]
      simp
  · rw [PBL.gN_setC_zero hB F v ε (S.G.r + 1) a P Q hloc]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hPl : D.IsLocPt P (S.G.r + 1)
    · have hQl : ¬ D.IsLocPt Q (S.G.r + 1) := fun h => hloc ⟨hPl, h⟩
      have hQs : ¬ D.IsLocPt (PBL.stdS S Q) (S.G.r + 1) := fun h =>
        hQl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S Q) hQs, map_zero, smul_zero,
        inner_zero_left, mul_zero]
    · have hPs : ¬ D.IsLocPt (PBL.stdS S P) (S.G.r + 1) := fun h =>
        hPl ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h)
      unfold KB.Pl.V
      dsimp only
      rw [vecV_nonloc (p v).T.base (p v).ν' (p v).m₀ (Fe i.1) (PBL.stdS S P) hPs, map_zero, smul_zero,
        inner_zero_right, mul_zero]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

section

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem sliceFamJF_cpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (j : ℕ)
    (Bs : B.RealPlaceData P.k (P.r - j) Wp Wq) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt (JC.parLev P j) Bs.z Bs.z' F) : KB.CptCoef Bs F := by
  obtain ⟨⟨hCC, ε, hε, hεG⟩, hcpt⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hCC 0 m).choose_spec.1), ?_, ε, hε, hεG⟩
  have hcont : Continuous (fun g : B.Mat P.k (P.r - j) => B.gN g) := by
    unfold B.gN
    fun_prop
  obtain ⟨R, hR⟩ := (hcpt.isCompact.image hcont).bddAbove
  refine ⟨R, fun g _ hg => hR ⟨g, subset_tsupport F hg, rfl⟩⟩

private theorem liftVec_injective_apply {k i r' : ℕ} {v w : Fin (2 * r' + k + 1) → ℂ}
    (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext q
  have hq := congrFun h ⟨q.1 + i, by omega⟩
  simp only [liftVec] at hq
  rw [dite_eq_left ⟨by simp, by simp; omega⟩, dite_eq_left ⟨by simp, by simp; omega⟩] at hq
  simpa using hq

private theorem castM_castM_eq_castM_trans {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (h3 : a = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM h3 g := by
  subst h1 h2
  rfl

theorem slice_family_orbital : SliceFamJF := by
  intro Wp Wq _ _ _ _ _ _ P T _ hN j hj _ _ F hF t ht γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hC := sliceFamJF_cpt P j (T.bs j) F hF
  set c : ℂ := ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) with hc
  let f0 : B.Mat P.k (P.r - (j + 1)) → Wq →L[ℂ] Wp := (B.GV P.k (P.r - (j + 1))).indicator fun g =>
    ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
        F ((rn1 e xx.1)⁻¹ * mc e t g * rn1 e xx.2)
      ∂(U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))
  have hsf : sliceFam T j hj F t = fun g => c • f0 g := by
    funext g
    simp only [sliceFam, f0, Set.indicator]
    split_ifs
    · rfl
    · rw [smul_zero]
  rw [hsf, JCx2.bc_JF_smul]
  congr 1
  obtain ⟨hW1, hW1', hN1⟩ := hN j (by omega)
  obtain ⟨hW0, hW0', hN0⟩ := hN (j + 1) hj
  refine jfStep P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (T.bs j) (T.bs (j + 1)) ?_ ?_ ?_ ?_
    hW1 hW1' hW0 hW0' hN1 hN0 F f0 t ht hC ?_ γ hγ hΩ
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z_lev (j + 1) hj]
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z'_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z'_lev (j + 1) hj]
  · intro y
    rw [T.π_lev (j + 1) hj, T.π_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro y
    rw [T.π'_lev (j + 1) hj, T.π'_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro g hg
    simp [f0, Set.indicator, hg]

end Formalism.FourierDecayAlt.P.CutSH
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def bq (H : B.Mat k r) : B.Mat k r →ₗ[ℝ] B.Mat k r →ₗ[ℝ] B.Mat k r :=
  LinearMap.mk₂ ℝ (fun M N => Mᴴ * H * N)
    (fun M M' N => by simp [Matrix.conjTranspose_add, Matrix.add_mul])
    (fun c M N => by simp [Matrix.conjTranspose_smul])
    (fun M N N' => by simp [Matrix.mul_add])
    (fun c M N => by simp)

def bqL (H : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (B.Mat k r →ₗ[ℝ] B.Mat k r) ≃ₗ[ℝ] (B.Mat k r →L[ℝ] B.Mat k r)).toLinearMap ∘ₗ
      bq H)

theorem bqL_apply (H M N : B.Mat k r) : bqL H M N = Mᴴ * H * N := rfl

theorem tangent_eq {d : ℕ} {O : Set (Fin d → ℝ)} {κ : (Fin d → ℝ) → B.Mat k r} (hO : IsOpen O)
    (hκ : ContDiffOn ℝ ∞ κ O) (hG : ∀ y ∈ O, κ y ∈ B.GV k r) {x : Fin d → ℝ} (hx : x ∈ O)
    (v : Fin d → ℝ) :
    (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x + (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v = 0 := by
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hB := (bqL (Hpk k r)).hasDerivAt_of_bilinear (fun _ => hc) (fun _ => hc)
  have hmem : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ O := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
  have hev : (fun _ : ℝ => Hpk k r) =ᶠ[nhds 0]
      fun t : ℝ => bqL (Hpk k r) ((κ ∘ fun t : ℝ => x + t • v) t) ((κ ∘ fun t : ℝ => x + t • v) t) := by
    filter_upwards [hmem] with t ht
    rw [bqL_apply]
    exact (hG _ ht).symm
  have h2 := hB.congr_of_eventuallyEq hev
  have e := h2.deriv
  rw [deriv_const] at e
  simp only [Function.comp_apply, zero_smul, add_zero] at e
  have e' : (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v + (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x = 0 := e.symm
  exact (add_comm _ _).trans e'

theorem chart_id {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    fderiv ℝ Φ (κ x) (fderiv ℝ κ x v) = v := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, _⟩ := hC
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdΦ : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.contDiffAt (hU.mem_nhds (hκO x hx).2.1)).differentiableAt (by simp)
  have h1 := hdΦ.hasFDerivAt.comp x hd.hasFDerivAt
  have hev : (Φ ∘ κ) =ᶠ[nhds x] id := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (hκO y hy).2.2
  have h2 : HasFDerivAt (Φ ∘ κ) (ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  have := h1.unique h2
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L v) this

theorem vr_onto {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    ∃ Y : B.Mat k r, B.inLie k r Y ∧ VR κ Φ Y x = v := by
  have hG : ∀ y ∈ O, κ y ∈ B.GV k r := fun y hy => (hC.2.2.2.2.1 y hy).1
  have hg : (κ x)ᴴ * Hpk k r * κ x = Hpk k r := hG x hx
  have hdet : IsUnit (κ x).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH (hG x hx)
  have hT := tangent_eq hC.1 hC.2.2.1 hG hx v
  set g := κ x with hgdef
  set A := fderiv ℝ κ x v with hAdef
  refine ⟨g⁻¹ * A, ?_, ?_⟩
  · have e1 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
      calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg]
        _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * g := by rw [Matrix.mul_nonsing_inv g hdet]; simp
    have e2 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
      calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg]
        _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.mul_one]
    show (g⁻¹ * A)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * A) = 0
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2, ← Matrix.mul_assoc]
    exact hT
  · show fderiv ℝ Φ g (g * (g⁻¹ * A)) = v
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.one_mul]
    exact chart_id hC hx v

def ellL {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ) :
    B.Mat k r →ₗ[ℝ] ℝ where
  toFun X := ξ ⬝ᵥ VR κ Φ X x
  map_add' X Y := by simp only [VR, Matrix.mul_add, map_add (f := _), dotProduct_add]
  map_smul' c X := by simp only [VR, Matrix.mul_smul, map_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul]

theorem ellL_apply {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ)
    (X : B.Mat k r) : ellL κ Φ x ξ X = ξ ⬝ᵥ VR κ Φ X x := rfl

def cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) : B.Mat k r :=
  Matrix.of fun j i => ((ℓ (Matrix.single i j 1) : ℝ) : ℂ) - Complex.I * ((ℓ (Complex.I • Matrix.single i j 1) : ℝ) : ℂ)

theorem ell_single (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (i j : Fin (2 * r + k + 1)) (c : ℂ) :
    ℓ (Matrix.single i j c) = c.re * ℓ (Matrix.single i j 1) + c.im * ℓ (Complex.I • Matrix.single i j 1) := by
  have : (Matrix.single i j c : B.Mat k r) =
      c.re • (Matrix.single i j (1 : ℂ) : B.Mat k r) + c.im • (Complex.I • (Matrix.single i j (1 : ℂ) : B.Mat k r)) := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem re_trace_cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (X : B.Mat k r) : (Matrix.trace (cMat ℓ * X)).re = ℓ X := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]

  simp only [map_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, cMat, Matrix.of_apply, Complex.re_sum, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ell_single ℓ i j (X i j)]
  norm_num
  ring

theorem inLie_half (C : B.Mat k r) : B.inLie k r ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hH' : ∀ M : B.Mat k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have hHc : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r))ᴴ * Hpk k r +
    Hpk k r * ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHc,
    Matrix.conjTranspose_conjTranspose, hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH, hH',
    Matrix.mul_one]
  rw [← smul_add]
  have : Cᴴ * Hpk k r - Hpk k r * C + (Hpk k r * C - Cᴴ * Hpk k r) = 0 := by abel
  rw [this, smul_zero]

theorem re_trace_half (C X : B.Mat k r) (hX : B.inLie k r X) :
    (Matrix.trace ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r) * X)).re = (Matrix.trace (C * X)).re := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hX' : Hpk k r * (X * Hpk k r) = -Xᴴ := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have h2 := congrArg (· * Hpk k r) h
    simp only [Matrix.add_mul, Matrix.mul_assoc, hH, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_right h2
  have e1 : Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = -star (Matrix.trace (C * X)) := by
    calc Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = Matrix.trace (Hpk k r * (Cᴴ * Hpk k r * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Cᴴ * (Hpk k r * (X * Hpk k r))) := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = -Matrix.trace ((X * C)ᴴ) := by
          rw [hX', Matrix.mul_neg, Matrix.trace_neg, Matrix.conjTranspose_mul]
      _ = -star (Matrix.trace (C * X)) := by rw [Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub, e1, smul_eq_mul]
  simp [Complex.mul_re]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity


open ChartCovPf in
theorem chart_covariance_holds : ChartCov := by
  intro k r d O U κ Φ hC x hx ξ
  refine ⟨(1 / 2 : ℂ) • (cMat (ellL κ Φ x ξ) - Hpk k r * (cMat (ellL κ Φ x ξ))ᴴ * Hpk k r),
    inLie_half _, ?_, ?_⟩
  · intro hξ h0
    obtain ⟨Y, hY, hYv⟩ := vr_onto hC hx ξ
    have e := re_trace_half (cMat (ellL κ Φ x ξ)) Y hY
    rw [h0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, re_trace_cMat, ellL_apply, hYv] at e
    exact hξ (dotProduct_self_eq_zero.1 e.symm)
  · intro X hX
    rw [re_trace_half _ X hX, re_trace_cMat, ellL_apply]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def wsAdj {k r : ℕ} (L : List (ℂ × List (B.Mat k r))) (b : B.Mat k r → ℂ) (x : B.Mat k r) : ℂ :=
  (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x).sum

def CapAdjScalar : Prop :=
  ∀ (k r : ℕ) (Y : ℂ) (μ : Measure (Mt k r)), B.IsHaarOn (B.GV k r) μ → ∀ a b : B.Mat k r → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b →
    (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, a (Matrix.of x) * star (Q.CV k r (conj Y) b (Matrix.of x)) ∂μ

def CapAdjIntOfScalar : Prop := CapAdjScalar → CapAdjInt

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end
