module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle210
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle215
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle100
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle213
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle217
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle098
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRCentre
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle220
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle221
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem rhyp_nodes (hTR : TopRatio) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hC : 28 * Real.exp 1 ≤ Cc) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) {K d : ℕ} (haN : a.length + K ≤ S.Ntop) (grid : Fin K → Fin (d + 1) → ℝ)
    (hmem : ∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ)))
    (n : Fin K → Fin (d + 1))
    (hcut : KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a))
    (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) :
    RHyp (p v).l0 a e ρ (S.P v) (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
      (Real.sqrt (S.T * S.T'))⁻¹) (List.ofFn fun b => grid b (n b)) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  rw [hl0]
  refine rhyp_of _ a e ρ _ _ _ fun ys₁ y ys₂ hsplit => ?_
  obtain ⟨b₀, hb₀, rfl, hlen, hlater⟩ := ofFn_split (fun b => grid b (n b)) ys₁ y ys₂ hsplit

  have hc : KB.CutWord (D.parOf S v) (S.l + 1) ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a) := by
    rw [PBD.cutWord_iff] at hcut ⊢
    rw [PBF.plusW_eq, hsplit] at hcut
    have hsub : ((true, grid b₀ (n b₀)) :: KB.plusW ys₂ a).Sublist
        ((ys₁ ++ grid b₀ (n b₀) :: ys₂).map (fun y => (true, y)) ++ a) := by
      rw [PBF.plusW_eq, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
      exact List.sublist_append_right _ _
    exact ⟨fun x hx => hcut.1 x (hsub.subset hx), hcut.2.sublist hsub⟩
  have hgr : ∃ m, grid b₀ (n b₀) ∈ S.grid v m := ⟨_, hmem b₀ (n b₀)⟩
  have hl : (KB.plusW ys₂ a).length < S.Ntop := by
    rw [PBF.plusW_eq, List.length_append, List.length_map]; omega
  have hfar : ∀ x ∈ KB.plusW ys₂ a, (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - x.2| ∧
      (x.1 = false → (S.Ntop : ℝ) ^ 2 + 1 ≤ |grid b₀ (n b₀) - (x.2 - 1)|) := by
    intro x hx
    rw [PBF.plusW_eq, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hx
      obtain ⟨b', hb', rfl⟩ := hlater y' hy'
      refine ⟨?_, fun h => absurd h (by simp)⟩
      have := PBD.sep_grid S hGo v (hmem b₀ (n b₀)) (hmem b' (n b')) (by
        have : (b₀ : ℕ) < b' := hb'
        have hb'K := b'.isLt
        omega) (e := 0) (e' := 0) (by simp) (by simp)
      simpa using this
    · have hy : (false = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ grid b₀ (n b₀) ∈ S.grid v a') ∨
          (false = true ∧ grid b₀ (n b₀) ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, grid b₀ (n b₀)) x) :=
        Or.inl ⟨rfl, a.length + K - (b₀ : ℕ), by have := b₀.isLt; omega, by omega, hmem b₀ (n b₀)⟩
      obtain ⟨h1, h2⟩ := node_far hB v a ha (grid b₀ (n b₀)) false hy x hx
      simp only [Bool.false_eq_true, if_false] at h1 h2
      unfold PBD.nodeOf at h1 h2
      by_cases hx1 : x.1 = true
      · rw [if_pos hx1] at h1
        exact ⟨h1, fun h => absurd h (by simp [hx1])⟩
      · rw [if_neg hx1] at h1 h2
        rw [sub_add_cancel] at h2
        exact ⟨h2, fun _ => h1⟩
  have := hTR Cb Cc E Wp Wq S p f χ A₀ hB hC v (KB.plusW ys₂ a) (grid b₀ (n b₀)) hc hgr hl hfar
    (KB.firstSt ys₂ e) ρ
  exact this

end asm

end

end Formalism.FourierDecayAlt.P.PBL
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

theorem psi_cast {k a b : ℕ} (e : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV e v) c (D.castM e g) = psi k a v c g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

theorem top_construction : TopMk := by
  intro hC Wp Wq _ _ _ _ _ _ P p
  have hT := p.hT
  have hr : P.r ≤ P.r := le_rfl
  have e0 : P.r + (P.r - P.r) = P.r := by omega
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  obtain ⟨b, hbs, hbc, hκL, hκR⟩ := Formalism.FourierDecayAlt.P.CutEX.MkTopBump.bump_exists (k := P.k) (p := P.r) (ρ := P.r - P.r)
    (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem
  obtain ⟨β, hβs, hβi, hβK⟩ := Formalism.FourierDecayAlt.P.CutEXMT.top_truncation_construction P.r
  refine ⟨b, b, β, kapL (p.T.bs P.r).z b * kapR (p.T.bs P.r).z' b, hbs, hbc, hbs, hbc, mul_ne_zero hκL hκR, hβs,
    ?_, ?_⟩
  · intro K hK hKU
    obtain ⟨K', hK', hK'1, hK'2⟩ := hβK (Mt P.k (P.r - P.r)) K hK (fun q hq => (hKU hq).1)
    refine ⟨K', hK', fun q hq => ?_, hK'2⟩
    obtain ⟨hd, q₀, hq₀, he⟩ := hK'1 q hq
    exact ⟨hd, he ▸ (hKU hq₀).2⟩
  · intro Φ hΦL hΦU Z y hZ hy
    have hyG : (Matrix.of y : B.Mat P.k (P.r - P.r)) ∈ B.GV P.k (P.r - P.r) :=
      (Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).1 hy
    have hz : p.T.base.z' = D.castV e0 (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') := (p.T.z'_lev P.r hr).symm
    have hpsi : ∀ u : G.UT P.r → ℂ, CutEX.psiU p (G.upper u) =
        psi P.k (P.r + (P.r - P.r)) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z') cStd
          (U.muP P.k P.r (P.r - P.r) (G.upper u)) := by
      intro u
      unfold CutEX.psiU
      rw [hz]
      exact psi_cast e0 _ _ _
    have key := hC P.k P.r (P.r - P.r) P.r Wp Wq e0 hρ (p.T.bs P.r) p.T.base (p.T.z'_lev P.r hr)
      (p.T.π'_lev P.r hr) (hT P.r hr).1 (hT P.r hr).2.1 (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT P.r hr e0)
      (hT P.r hr).2.2 (hT 0 (Nat.zero_le _)).2.2 b b β Φ hbs.continuous hbc hbs.continuous hbc Z hZ
      (hβi Z hZ).1 (hβi Z hZ).2 y hyG (fun h1 hh1 h2 hh2 => hΦL Z y hy h1 hh1 h2 hh2)
      (fun u y' hy' => by
        rw [hΦU Z y' (G.upper u) hZ ((Formalism.FourierDecayAlt.P.CutEX.MkCptPf.glev_last_iff hρ _).2 hy')
          (Formalism.FourierDecayAlt.P.LeftFubiniLemmas.upper_isUpUni u), hpsi u])
    exact key

theorem mkTop_of_avgs (hR : RightAvg) (hL : LeftAvg) : CutEX.MkTop := mkTop_of_leaves hR hL top_construction

end Formalism.FourierDecayAlt.P.CutMK
end
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MeasJ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapS (l : Fin r) (c : Fin r → ℂ) (q : (ℂ × Cf r l.succ) × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue l.succ (Function.update c l q.1.1) q.1.2, Matrix.of q.2)

theorem glueMapS_continuous (l : Fin r) (c : Fin r → ℂ) : Continuous (glueMapS (k := k) l c) := by
  unfold glueMapS
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun m => ?_
    by_cases h : (l.succ : Fin (r + 1)).val ≤ m.val
    · simp only [glue, h, dif_pos]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · simp only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]
      by_cases hm : m = l
      · simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop
      · simp only [hm, if_false, ite_false] <;> fun_prop
  · exact continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop

theorem measurableSet_glueMapS_DomR (l : Fin r) (c : Fin r → ℂ) :
    MeasurableSet (glueMapS (k := k) l c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapS_continuous l c)).measurableSet

end MeasJ

theorem spectral_measurability : JSMeas := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ
  have hmaps : Set.MapsTo (glueMapS (k := k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0 :=
    radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_family_apply_holds : WFamApp := by
  intro d α L F c v x
  simp [wfam, WOp.app, List.map_append, List.sum_append, vfW, Function.comp_def]

theorem word_family_symbol_holds : WFamSymb := by
  intro d α L F c j x ξ τ hj hτ
  have h0 : ¬ (0 = j) := by omega
  simp only [wfam, WOp.symb, List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, h0, if_false, add_zero]
  congr 1
  refine List.map_congr_left (fun t ht => ?_)
  simp only [Function.comp_apply, List.length_map]
  split_ifs with hl
  · congr 1
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left (fun X hX => hτ t ht X hX))
  · rfl

theorem trace_real_lie_holds : TrRealLie := by
  intro k r A X hA hX
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose k r
  have hH2 : Hpk k r * Hpk k r = 1 := WeylGroupFacts.hpk_sq
  have eA : Aᴴ = -(Hpk k r * A * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hA
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have eX : Xᴴ = -(Hpk k r * X * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hX
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have hstar : star (Matrix.trace (A * X)) = Matrix.trace (A * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, eX, eA, neg_mul_neg]
    calc Matrix.trace (Hpk k r * X * Hpk k r * (Hpk k r * A * Hpk k r))
        = Matrix.trace (Hpk k r * (X * (Hpk k r * Hpk k r) * A * Hpk k r)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * (Hpk k r * Hpk k r) * A * Hpk k r) * Hpk k r) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * A) := by simp only [Matrix.mul_assoc, hH2, Matrix.mul_one]
      _ = Matrix.trace (A * X) := Matrix.trace_mul_comm _ _
  exact Complex.conj_eq_iff_re.mp hstar

theorem smooth_on_levels_holds : CkLevOn := by
  intro k r m Dm E _ _ f hf g₀ hg₀
  have hg₀' : g₀ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hg₀.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg₀.2⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀'
  exact ⟨U, F, hU, hgU, by exact_mod_cast hF, fun g hg hgG => hfF g hg ⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩

theorem operator_capelli_vector : OpCVOf := opCVOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_right_capelli : OpCapROf := opCapROf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_left_capelli : OpCapLOf := opCapLOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section consts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamLift (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) *
    J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)

theorem g_cast' (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem norm_lamB' (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (b s : ℕ) :
    ‖lamB S b s‖ = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) := by
  have hg' : (0 : ℝ) < (S.g : ℝ) := by rw [g_cast']; exact hg
  rw [norm_lamB S hg' b s, g_cast', zpow_neg, ← inv_zpow, inv_div]

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq'] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem lamLift_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) : 0 ≤ lamLift S b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v false
  unfold lamLift
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_lift (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (hbs : b + s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamLift S b s v ∧ lamLift S b s v ≤ S.base.szL b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 b s (Real.exp 1)
    ((28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s)) hb (Real.exp_pos 1).le le_rfl hcg le_rfl
  have hdec : decide (b = 1 ∧ s + 1 = 1) = false := decide_eq_false (by omega)
  rw [hdec] at h
  refine ⟨lamLift_nonneg hB b s v, ?_⟩
  show lamLift S b s v ≤ (if b + s ≤ S.G.r + 1 then _ else _)
  rw [if_pos hbs]
  unfold lamLift
  exact h

theorem lift_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (b s j K : ℕ) (hjb : b + s = j + 1)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ)
    (hl1 : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * (j - s) + s)) :
    (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ (lamLift S b s v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  rw [norm_lamB' S hg b s]
  have hexp : 2 * (j - s) + s = 2 * (b - 1) + s := by omega
  have hl1' : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := fun c =>
    (hl1 c).trans_eq (by rw [hexp, ntop_eq_N', len_eq'])
  unfold lamLift
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ cg ^ K := by
    calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ ∏ _c : Fin K, cg :=
          Finset.prod_le_prod₀ (fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun c _ => hl1' c
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ c, ∑ i, |F7.lagCo (grid c) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

theorem norm_u (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s K : ℕ) :
    ‖((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K)‖ = 1 := by
  rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_pow,
    norm_neg, norm_one, one_pow, mul_one, mul_inv_cancel₀ (norm_ne_zero_iff.2 (lamB_ne S hg b s)), one_pow]

end consts

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem left_covariance_chart_holds : CovL := by
  intro k r d O U κ Φ hC x hx ξ Ξ₀ _hΞ₀ hcov X hX
  have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  have hY : B.inLie k r ((κ x)⁻¹ * X * κ x) := by
    unfold B.inLie at hX ⊢

    have e1 : ((κ x)⁻¹ * X * κ x)ᴴ * Hpk k r = (κ x)ᴴ * (Xᴴ * Hpk k r) * κ x := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← hHg]
    have e2 : Hpk k r * ((κ x)⁻¹ * X * κ x) = (κ x)ᴴ * (Hpk k r * X) * κ x := by
      simp only [← Matrix.mul_assoc]
      rw [← hgH]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]
  have hV : VL κ Φ X x = VR κ Φ ((κ x)⁻¹ * X * κ x) x := by
    show fderiv ℝ Φ (κ x) (X * κ x) = fderiv ℝ Φ (κ x) (κ x * ((κ x)⁻¹ * X * κ x))
    rw [show κ x * ((κ x)⁻¹ * X * κ x) = X * κ x by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hig, Matrix.one_mul]]
  have ht : Matrix.trace (Ξ₀ * ((κ x)⁻¹ * X * κ x)) = Matrix.trace (κ x * Ξ₀ * (κ x)⁻¹ * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hV, hcov _ hY, ht]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_K_invariance_holds : GTRRotK :=
  gTRRotK_of_mat_fin_centre_sec_ode_wirt rotation_matrix_form_holds rotation_finite_from_matrix rotation_centre_condition rotation_section_holds rotation_ode_holds rotation_wirtinger_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
