module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle100
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle160
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle137
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

theorem sec_at (hR : SARadSec) (hD : SADescend) (hC : SACover)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (U : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ K ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'), Gauge.trJB P Bs e K = U := by
  obtain ⟨Φ, hΦ, hval⟩ := hR Wp Wq P Bs hpl e he U
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ := hD Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem Φ hΦ
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r Bs.z Bs.z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ := hC P.k P.r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  refine ⟨K, ?_, ?_⟩
  · obtain ⟨hs, hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  · funext ρ
    have hraw : Gauge.rawJ P Bs e K ρ = (U ρ : MA.Qp P.r P.TT → ℂ) := by
      funext q
      have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
        rw [Gauge.GC.SSTr.tz_eq P Bs hpl]; exact q.2.2
      have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
        Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
      have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
        unfold Q.GGl
        rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
        linarith
      have hζ' : P.TT < Complex.normSq q.1.2 := q.2.2
      have horth := (he.2 q.1.2 hζ').2.1
      have hwpos : 0 < Real.sqrt (MA.wq P.k q.1 P.TT) := Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos q.2)
      have hw : ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      simp only [Gauge.rawJ]
      rw [Gauge.tc_gq, (hKv q.1.1 q.2.1 _ hG hGG).2, hval q, Gauge.tc_hsVec_smul, inner_smul_right,
        Gauge.tc_hsVec_sum, inner_sum]
      simp only [Gauge.tc_hsVec_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      push_cast
      field_simp
    show MA.toSm P (Gauge.rawJ P Bs e K ρ) = U ρ
    have hm : Gauge.rawJ P Bs e K ρ ∈ MA.smSub P.r P.TT := by rw [hraw]; exact (U ρ).2
    rw [Gauge.toSm_of_mem P hm]
    apply Subtype.ext
    exact hraw

theorem sASection_of_parts (hR : SARadSec) (hD : SADescend) (hC : SACover) : SASection := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he U _
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨K, hK, hKU⟩ := sec_at hR hD hC (D.parOf S v) (T v).base hpl e he U
  refine ⟨K, ?_, hKU⟩
  show K ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
  exact hK

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section comp

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

theorem op_comp (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → (ι → E)}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) (i : ι) {g : Mat k r} (hg : g ∈ GV k r) :
    P.B4.op b X (fun h => G h i) g = P.B4.op b X G g i := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g hg
  have hc0 : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U := by simpa using hc
  have e1 := P.B4.op_eq_op' 0 b hU hc0 hff hX g hgU hg
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  have hc' : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) (fun h => f' h i) U :=
    pr.contDiff.comp_contDiffOn hc0
  have hff' : ∀ h ∈ U, h ∈ GV k r → (fun h => G h i) h = (fun h => f' h i) h := fun h hU' hG' => by
    simp only [hff h hU' hG']
  have e2 := P.B4.op_eq_op' 0 b hU hc' hff' hX g hgU hg
  rw [e2, e1]
  unfold P.B4.op'
  have hd : DifferentiableAt ℝ f' g :=
    (hc0.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hfd : HasFDerivAt (fun h => f' h i) (pr.comp (fderiv ℝ f' g)) g :=
    pr.hasFDerivAt.comp g hd.hasFDerivAt
  rw [hfd.fderiv]
  rfl

theorem W_comp (w : List (Bool × Mat k r)) (hw : P.B4.AllLie w) {G : Mat k r → (ι → E)}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) (i : ι) :
    ∀ g ∈ GV k r, P.B4.W w (fun h => G h i) g = P.B4.W w G g i := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hl : w.length ≤ (x :: w).length := by simp
    have hl1 : 1 + w.length ≤ (x :: w).length := by simp; omega
    rw [P.B4.W_cons, P.B4.W_cons,
      P.B4.op_congr x.1 (hw x List.mem_cons_self) (ih hw' (P.B4.ckOn_mono hl hG)) g hg]
    exact op_comp x.1 (hw x List.mem_cons_self) (P.B4.smooth_on_of_word_derivatives w hw' 1 (P.B4.ckOn_mono hl1 hG)) i hg

theorem ckOn_comp {m : ℕ∞} {G : Mat k r → (ι → E)} (hG : CkOn m (GV k r) G) (i : ι) :
    CkOn m (GV k r) (fun h => G h i) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g₀ hg₀
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  exact ⟨U, fun h => f' h i, hU, hgU, pr.contDiff.comp_contDiffOn hc, fun g hg hgG => by simp only [hff g hg hgG]⟩

theorem ccle_comp {A c : ℝ} {m : ℕ} {G : Mat k r → (ι → E)} (hG : CCle A m G c) (i : ι) :
    CCle A m (fun h => G h i) c := by
  refine ⟨ckOn_comp hG.1 i, fun u v hu hv hl g hg => ?_⟩
  have hw : P.B4.AllLie (P.B4.lr u v) := by
    intro x hx
    simp only [P.B4.lr, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  have hlen : (P.B4.lr u v).length ≤ m := by simp [P.B4.lr]; omega
  have e : dLR u v (fun h => G h i) g = dLR u v G g i := by
    rw [P.B4.dLR_eq, P.B4.dLR_eq]
    exact W_comp _ hw (P.B4.ckOn_mono hlen hG.1) i g hg
  rw [e]
  refine le_trans ?_ (hG.2 u v hu hv hl g hg)
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v G g) i) hgN

end comp

section beta

open Formalism.FourierDecayAlt.P.JCx2 Filter

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congr_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [sq_jf_congr D h hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end beta

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

theorem form_model : Formalism.FourierDecayAlt.P.FormNormSumIdentities.FormModel := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg j w a mm ε' Sg hε' ha hmm hmm5 hSg V _ _ Mo
  let comp : V → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun u e γ => Mo.ev u γ e
  have hcc : ∀ u e, CCle a mm (comp u e) ‖u‖ := fun u e => FormNormSumIdentities.ccle_comp (Mo.mem u) e
  have hin : ∀ u e, InCC a mm (comp u e) := fun u e => ⟨_, hcc u e⟩
  have hadd : ∀ u u', comp (u + u') = comp u + comp u' := by
    intro u u'; funext e γ; simp [comp, map_add (f := _)]
  have hsmul : ∀ (c : ℂ) u, comp (c • u) = c • comp u := by
    intro c u; funext e γ; simp [comp, map_smul]
  have hzero : comp 0 = 0 := by funext e γ; simp [comp]
  have hS := fun x x' y c hx hx' hy => JCx4.formLev_sesq_core P0 T sg j w a mm ha hmm x x' y c hx hx' hy
  have h0l : ∀ u', D.formLev T sg j w 0 (comp u') = 0 := by
    intro u'
    have h := (hS (comp 0) (comp 0) (comp u') 1 (hin 0) (hin 0) (hin u')).1
    rw [hzero, one_smul, add_zero, one_mul] at h
    linear_combination -h
  have h0r : ∀ u, D.formLev T sg j w (comp u) 0 = 0 := by
    intro u
    have h := (hS (comp 0) (comp 0) (comp u) 1 (hin 0) (hin 0) (hin u)).2
    rw [hzero, one_smul, add_zero, map_one, one_mul] at h
    linear_combination -h
  let Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u u' => D.formLev T sg j w (comp u) (comp u'))
    (fun u₁ u₂ u' => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u') 1 (hin u₁) (hin u₂) (hin u')).1
      rw [one_smul, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u) (comp u') c (hin 0) (hin u) (hin u')).1
      rw [hzero, zero_add, h0l, zero_add] at h
      exact h)
    (fun u u₁ u₂ => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u) 1 (hin u₁) (hin u₂) (hin u)).2
      rw [one_smul, map_one, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u') (comp u) c (hin 0) (hin u') (hin u)).2
      rw [hzero, zero_add, h0r, zero_add] at h
      exact h)
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P0 T sg j w a ha
  have hN0 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
  refine ⟨Bf, Real.sqrt Cf, Real.sqrt_nonneg _, fun u => ?_, ?_⟩
  · have hb := hCf (comp u) (comp u) ‖u‖ ‖u‖
      (fun b => pd_ccle_mono (by linarith) hmm5 (hcc u b))
      (fun b => pd_ccle_mono (by linarith) (by omega) (hcc u b))
    have e : Bf u u = D.formLev T sg j w (comp u) (comp u) := rfl
    rw [e]
    calc (D.formLev T sg j w (comp u) (comp u)).re ≤ ‖D.formLev T sg j w (comp u) (comp u)‖ := Complex.re_le_norm _
      _ ≤ Cf * ‖u‖ * ‖u‖ := hb
      _ = (Real.sqrt Cf * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hCf0]; ring
  · intro u u' x x' ε'' hε'' hx hx' hxu hxu'
    show D.formLev T sg j w (comp u) (comp u') = D.formLev T sg j w x x'
    unfold D.formLev
    refine Finset.sum_congr rfl fun e _ => ?_
    have hRR := JCx4.ma_hS P0 T sg j w
    have hmmU : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 w.length :=
      pd_thr_mm P0 j w.length _ le_rfl
    have hinx : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x b) :=
      fun b => sq_inCC_mono le_rfl (by omega) (hx b).2.1
    have hinu : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (comp u b) :=
      fun b => sq_inCC_mono ha (by omega) (hin u b)
    have hloc : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T sg j w) (comp u) e g =
        D.actOp (D.RRlev T sg j w) x e g := by
      intro g hg
      rw [JCx4.ma_actOp_eq, JCx4.ma_actOp_eq]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hA : P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ) + ((2 * w.length : ℕ) : ℝ) =
          P5.Auser P0 w.length + 1 := by ring
      have hm : 0 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length =
          (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length := by ring
      refine (hRR e b).2.2 (P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ)) 0 (comp u b) (x b)
        (by rw [hA, hm]; exact hinu b) (by rw [hA, hm]; exact hinx b) (fun γ hγ => hxu b γ hγ) g hg
    rw [sq_beta_congr (T.bs j) hloc]
    exact FormNormSumIdentities.beta_congr_right (T.bs j) (fun γ hγ => hxu' e γ hγ)

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cV_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

section fold

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}

theorem ckOn_of_ffl {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) :
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Dm ∩ B.GV k r) J := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hg₀.2, hg₀.1⟩
  exact ⟨U, F, hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hg hgG => he g hg (Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hgG)⟩

theorem letter_congr (hCL : CVLocal) (hDm : IsOpen Dm) {J₁ J₂ : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (h₁ : J₁ ∈ Q.FFl k r z z' π π' 0 Dm) (h₂ : J₂ ∈ Q.FFl k r z z' π π' 0 Dm)
    (he : ∀ g ∈ Q.Glev k r 0 ∩ Dm, J₁ g = J₂ g) (Y : ℝ) (s : ℂ) :
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, (s • Q.CV k r (Y : ℂ) J₁) g = (s • Q.CV k r (Y : ℂ) J₂) g := by
  intro g hg
  have := hCL k r _ Dm J₁ J₂ (Y : ℂ) hDm (ckOn_of_ffl h₁) (ckOn_of_ffl h₂)
    (fun x hx => he x ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.2, hx.1⟩) g ⟨hg.2, hg.1.1⟩
  simp only [Pi.smul_apply, this]

theorem letter_swap (hDm : IsOpen Dm) {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm)
    (x y : ℝ) (s : ℂ) : ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      (s • Q.CV k r (x : ℂ) (s • Q.CV k r (y : ℂ) J)) g = (s • Q.CV k r (y : ℂ) (s • Q.CV k r (x : ℂ) J)) g := by
  intro g hg
  simp only [cV_smul, Pi.smul_apply]
  unfold Q.CV
  rw [Formalism.FourierDecayAlt.P.capelli_commutation _ k r 0 Dm J hDm hJ.1 g hg]

theorem foldCV_append (s : ℂ) (l₁ l₂ : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)) :
    foldCV k r s (l₁ ++ l₂) J = foldCV k r s l₁ (foldCV k r s l₂ J) := by
  unfold foldCV; rw [List.foldr_append]

end fold

theorem foldRev_of (hCL : CVLocal) : FoldRev := by
  intro k r Wp Wq _ _ _ _ z z' π π' Dm hDm hcl J hJ s a
  have hcomm : ∀ (b : List C.Letter) (J : Q.Mx k r → (Wq →L[ℂ] Wp)), J ∈ Q.FFl k r z z' π π' 0 Dm →
      ∀ x : C.Letter, ∀ g ∈ Q.Glev k r 0 ∩ Dm,
        foldCV k r s b (s • Q.CV k r (x.2 : ℂ) J) g = (s • Q.CV k r (x.2 : ℂ) (foldCV k r s b J)) g := by
    intro b
    induction b with
    | nil => intro J _ x g _; rfl
    | cons y b ih =>
      intro J hJ x g hg
      have h1 := letter_congr hCL hDm (foldCV_mem hcl (hcl J hJ x.2 s) s b)
        (hcl _ (foldCV_mem hcl hJ s b) x.2 s) (ih J hJ x) y.2 s g hg
      have h2 := letter_swap hDm (foldCV_mem hcl hJ s b) y.2 x.2 s g hg
      rw [foldCV_cons, h1, h2]
      rfl
  induction a generalizing J with
  | nil => intro g _; rfl
  | cons x a ih =>
    intro g hg
    rw [List.reverse_cons, foldCV_append]
    rw [ih (foldCV k r s [x] J) (hcl J hJ x.2 s) g hg]
    exact hcomm a J hJ x g hg

theorem folding_reversal_holds : FoldRev := foldRev_of coefficient_vector_locality

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAFFStable_of_adjComm (hA : AdjComm) : JAFFStable :=
  jAFFStable_of_parts germ_operators_holds extension_locality_holds smooth_operators_holds hA equivariant_operators_holds positive_domain_condition_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniReduction

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leftFubini_of_core (hC : LeftFubiniLemmas.CoreLF) : LeftFubiniLemmas.LeftFubini := by
  intro k r Wp Wq _ _ _ _ _ _ T hT j hj hj1 a ha
  obtain ⟨hab, rfl⟩ := ha
  have e : D.ptSize a + (r - D.ptSize a) = r := by omega
  have hd : ∀ q, D.ptDiag a q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hab q q.2
  obtain ⟨X, hX, μ, ℓ, sx, hsx, hmain⟩ := hC k (D.ptSize a) (r - D.ptSize a) r e hj1 (D.ptPerm a) (D.ptDiag a) hd
    Wp Wq (T.bs (D.ptSize a)) T.base (T.z_lev _ hj) (T.z'_lev _ hj) (T.π'_lev _ hj) (hT _ hj).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' T hT _ hj e) (hT _ hj).2.2 (hT 0 (Nat.zero_le r)).2.2
  refine ⟨X, hX, μ, ℓ, sx, hsx, fun g hg H hH hR => ?_⟩
  have hx : ∀ (h1 : D.ptSize a ≤ r) (h2 : r - D.ptSize a = r - D.ptSize a),
      LeftFubiniLemmas.levelZeroPointOver a h1 (D.castM h2 g) = D.castM e (U.mMap k (D.ptSize a) (r - D.ptSize a)
        (U.hMat (D.ptPerm a) (D.ptDiag a)) g) := by
    intro h1 h2
    unfold LeftFubiniLemmas.levelZeroPointOver
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hs : ∀ h2 : r - D.ptSize a = r - D.ptSize a,
      D.castF h2 (D.sliceAt k r T.base.z T.base.z' H a) =
        U.PhiFun (s := 0) k (r - D.ptSize a) (D.ptPerm a) (D.ptDiag a) (D.castV e.symm T.base.z)
          (D.castV e.symm T.base.z') (D.castF e H) (fun a => a.elim0) := by
    intro h2
    funext y
    unfold D.castF
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, D.sliceAt, dite_eq_left hj]
    rfl
  simp only [hx, hs]
  exact hmain g hg H hH hR

end Formalism.FourierDecayAlt.P.LeftFubiniReduction
end
end

section

namespace Formalism.FourierDecayAlt.P

def PBI.HeadTopOfParts : Prop := PBI.HighestUnipotentIntegral → PBI.Exh → PBI.HeadWeightAt → KB.HeadTop

theorem head_top_of_parts : PBI.HeadTopOfParts := fun hU5 hExh hW =>
  head_top_of_correspondence (head_correspondence_of_parts levFrameExists_statement (head_vector_of_parts hU5 hExh)
    (head_types_of_types_at (head_types_at_of_weight hW)))

end Formalism.FourierDecayAlt.P
end
