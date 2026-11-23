module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle109
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle138
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle169
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem sAPairOne_of_parts (hZ : SAZero) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) :
    SAPairOne := by
  obtain ⟨C1, hZ'⟩ := hZ
  obtain ⟨C2, hL'⟩ := hL
  obtain ⟨C3, hE'⟩ := hE
  obtain ⟨C4, hJC'⟩ := hJC
  obtain ⟨C5, hB3'⟩ := hB3
  refine ⟨max C1 (max C2 (max C3 (max C4 C5))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θ hΘ K hK J hJ hΘK hΘJ hKt
  have mono : ∀ c : ℝ, c ≤ max C1 (max C2 (max C3 (max C4 C5))) → BuiltOW c S T f χ ν' m₀ top A₀ :=
    fun c h => ⟨isBuiltPlace_mono h hB.1, hB.2⟩
  have hB1 := mono C1 (le_max_left _ _)
  have hB2 := mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB3 := mono C3 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hB4 := mono C4 (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hB5 := mono C5 (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs

  set Cs : Set (MA.E (D.parOf S v).r) :=
    ⋃ π, tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
      MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) with hCsdef
  have hCc : IsCompact Cs := isCompact_iUnion fun π => (hKt π).1
  have hCQ : Cs ⊆ Qs := Set.iUnion_subset fun π => (hKt π).2
  have hCcl : IsClosed Cs := hCc.isClosed
  have hK0 : ∀ y ∈ Qs, y ∉ Cs → K (B.gq (T v).base y) = 0 := by
    intro y hy hyC
    refine hZ' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he K hK y hy fun π => ?_
    have hn : y ∉ tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) := fun h => hyC (Set.mem_iUnion.2 ⟨π, h⟩)
    have h0 := image_eq_zero_of_notMem_tsupport hn
    simp only [MA.ext] at h0
    first
    | exact h0 hy
    | exact (dif_pos hy).symm.trans h0
  have hΘK0 : ∀ y ∈ Qs, y ∉ Cs → B.opApply Θ K (B.gq (T v).base y) = 0 := fun y hy hyC =>
    hL' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v Θ hΘ K hK (Qs \ Cs) ((MA.Qset_open _ _).sdiff hCcl)
      Set.sdiff_subset (fun y' hy' => hK0 y' hy'.1 hy'.2) y ⟨hy, hyC⟩
  refine ⟨fun π => ?_, ?_⟩
  ·
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he (B.opApply Θ K) hΘK π
    have hsupp : Function.support (MA.ext ((trJ S T v e (B.opApply Θ K) π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) ⊆ Cs := by
      intro y hy
      by_contra hyC
      apply hy
      by_cases hyQ : y ∈ Qs
      · simp only [MA.ext]
        unfold trJ
        rw [En.toSm_val_of_mem _ hsm]
        simp [hΘK0 y hyQ hyC, GA.hsVec_zero']
      · simp only [MA.ext]
        first
        | exact fun h => absurd h hyQ
        | exact dif_neg hyQ
    have hts := closure_minimal hsupp hCcl
    exact ⟨hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCQ⟩
  ·
    obtain ⟨F₁, U₁, -, hCU₁, hF₁s, hF₁c, hF₁O, hF₁e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v K hK Cs hCc hCQ
    obtain ⟨F₂, U₂, hU₂o, hCU₂, hF₂s, hF₂c, hF₂O, hF₂e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v J hJ Cs hCc hCQ
    have hKF₁ : ∀ y ∈ Qs, K (B.gq (T v).base y) = B.JF (T v).base F₁ (B.gq (T v).base y) := by
      intro y hy
      by_cases hyU : y ∈ U₁
      · exact ((hF₁e y hy).1 hyU).symm
      · have hyC : y ∉ Cs := fun h => hyU (hCU₁ h)
        rw [hK0 y hy hyC, (hF₁e y hy).2 (hK0 y hy hyC)]
    have hc1 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₁ hF₁s hF₁c hF₁O Set.univ K isOpen_univ hK
      (fun y hy _ => hKF₁ y hy)
    have hc2 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₂ hF₂s hF₂c hF₂O U₂ J hU₂o hJ
      (fun y hy hyU => ((hF₂e y hy).1 hyU).symm)
    obtain ⟨hF₁5, hF₂5, hΘF₁5, hΘF₂5, hβ⟩ :=
      hB3' E Wp Wq S T f χ ν' m₀ top A₀ hB5 v Θ hΘ F₁ F₂ hF₁s hF₁c hF₁O hF₂s hF₂c hF₂O
    have hLp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he (B.opApply Θ K) J (B.opApply Θ F₁) F₂
      hΘK hJ hΘF₁5 hF₂5 (Filter.Eventually.of_forall fun y hy => ⟨(hc1 y hy trivial).1, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hΘK0 y hy hyC)
        exact ((hF₂e y hy).1 (hCU₂ hyC)).symm⟩)
    have hRp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he K (B.opAdj Θ J) F₁ (B.opAdj Θ F₂)
      hK hΘJ hF₁5 hΘF₂5 (Filter.Eventually.of_forall fun y hy => ⟨hKF₁ y hy, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hK0 y hy hyC)
        exact (hc2 y hy (hCU₂ hyC)).2⟩)
    rw [hLp, hRp]
    exact hβ

theorem sAPairL_of_parts (hF : JAFFStable) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) : SAPairL :=
  sAPairL_of_one hF (sAPairOne_of_parts self_adjoint_zero_holds hL hE hJC hB3)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

namespace SSEn

theorem coe_sum_apply {r : ℕ} {TT : ℝ} {ι : Type} (s : Finset ι) (g : ι → MA.SmQ r TT) (q : MA.Qp r TT) :
    Subtype.val (∑ i ∈ s, g i) q = ∑ i ∈ s, Subtype.val (g i) q := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

theorem ss_entry_apply (P : M.Par) (l : ℕ) (ρ π' : M.Ty P) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 f) q =
      (if M.Up P l π' ρ then ((Real.sqrt (M.Nrm P l π') : ℝ) : ℂ) else 0) * (f : MA.Qp P.r P.TT → ℂ) q := by
  simp only [MA.SS, Matrix.of_apply]
  split_ifs with h
  · rfl
  · rw [zero_mul]
    rfl

end SSEn

open SSEn in
theorem second_shift_entry_holds : SSn.Rep.Core.SSEntry := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hSSF l hl S hS ζ hζ π ρ
  obtain ⟨hpl, hL, hSt, hRel, hQQ⟩ := hA
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := Gauge.GC.tz_TT P Bs hpl
  have hRB := Gauge.GC.radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero

  have hsec : ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e π q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨((he.1 π).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 π
    · simp [Set.indicator_of_notMem hq]
  obtain ⟨Ψ0, hΨ0, hΨr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ hsec
  let Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Ψ0, hΨ0⟩
  have hΨ : (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) = e π ζ := by
    have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ⟩
    have h := congrFun hΨr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h

  have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
      ((Gauge.GC.trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
        Gauge.rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
    Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (Gauge.GC.radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
  let q : MA.Qp P.r P.TT := ⟨((c0, ζ) : MA.E P.r), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hw := Gauge.GC.wRc_ne P hζ

  have e1 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) := by
    refine (congrFun (hv ((d.SS l).1 Ψ) ρ) q).trans ?_
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((((d.SS l).1 Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hS Ψ c0 hc0 ζ hζ, hΨ]

  have e2 : Subtype.val (Gauge.GC.trR P Bs e ((d.SS l).1 Ψ) ρ) q =
      ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q := by
    refine (congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => Subtype.val (F ρ) q) (hSSF l hl Ψ).1).trans ?_
    exact coe_sum_apply _ _ _
  have hterm : ∀ π' : M.Ty P, Subtype.val (Gauge.GC.trR P Bs e Ψ π') q =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * (if π' = π then 1 else 0) := by
    intro π'
    rw [congrFun (hv Ψ π') q]
    show ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e π' ζ))
      (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ))) = _
    rw [hΨ, (he.2 ζ hζ).2.1 π' π]
  have e3 : ∑ π', Subtype.val ((MA.SS P (MA.DQ P) l ρ π').1 (Gauge.GC.trR P Bs e Ψ π')) q =
      (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) * ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) := by
    simp only [ss_entry_apply, hterm]
    rw [Finset.sum_eq_single π (fun π' _ hne => by simp [hne]) (fun h => absurd (Finset.mem_univ π) h)]
    simp
  have h2 : ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
      ((Gauge.wR P.k P.TT ζ : ℝ) : ℂ) *
        (if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0) := by
    rw [← e1, e2, e3, mul_comm]
  exact mul_left_cancel₀ hw h2

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem repLin_nice {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp))
    (hG : GoodFam T j G) (t : ℂ) (ht : t ≠ 0) :
    ∃ ε, 0 < ε ∧ JC.NiceCoef (T.bs (j + 1)) ε (G t) := by
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 {t} isCompact_singleton (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact ht)
  have hsupp : ∀ γ, G t γ ≠ 0 → γ ∈ C := fun γ h => (hCε t rfl γ h).1
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t ht γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact ⟨ε, hε, hck, fun A' m' => JFxG.cptInCC_G hck hC (fun γ _ hγC => by
      by_contra h; exact hγC (hsupp γ h)) A' m', fun γ hγ hne => (hCε t rfl γ hne).2 hγ⟩

theorem representation_linear : RepLin := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j _ _ G G' hG hG' t ht a x hx
  obtain ⟨ε, hε, hN⟩ := repLin_nice T j G hG t ht
  obtain ⟨ε', hε', hN'⟩ := repLin_nice T j G' hG' t ht
  have hm : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G t) :=
    ⟨hN.1, hN.2.1, fun g hg hne => (min_le_left _ _).trans (hN.2.2 g hg hne)⟩
  have hm' : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G' t) :=
    ⟨hN'.1, hN'.2.1, fun g hg hne => (min_le_right _ _).trans (hN'.2.2 g hg hne)⟩
  have hom : wCell P.k (P.r - (j + 1)) (Fin.last (P.r - (j + 1))) x.1 * x.2 ∈
      JF.Om P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' :=
    TLB.wCell_om (Pa := JC.parLev P (j + 1)) (T.bs (j + 1)) hx
  have hs : B.JF (T.bs (j + 1)) (fun γ => a • G t γ) = a • B.JF (T.bs (j + 1)) (G t) :=
    funext fun h => JCx2.bc_JF_smul a (G t) h
  refine ⟨?_, ?_⟩
  · simp only [resG]
    rw [JCx2.bc_JF_add hm hm' hom, smul_add]
  · rw [hs, JCx2.rma_resG_smul]

end Formalism.FourierDecayAlt.P.CutSH
end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pOp l f₁ c = pOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pOp, wirt, ite_eq_left hc, hev.fderiv_eq]

theorem vAB_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (Q.vAB r Y i).1 f₁ c = (Q.vAB r Y i).1 f₂ c ∧ (Q.vAB r Y i).2 f₁ c = (Q.vAB r Y i).2 f₂ c := by
  intro i f₁ f₂ h
  induction i with
  | zero =>
    intro c hc
    exact ⟨h c hc, rfl⟩
  | succ i ih =>
    intro c hc
    by_cases hi : i < r
    · simp only [Q.vAB, dite_eq_left hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
        rw [(ih c hc).1, (ih c hc).2, pOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [ciOp]
        rw [(ih c hc).1]
    · simp only [Q.vAB, dite_eq_right hi]
      exact ih c hc

end loc

section jd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_dinv (Bs : B.RealPlaceData k r Wp Wq) (H : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.JF Bs (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g =
      (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • B.JF Bs H g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last _))⁻¹ • H x) g ∂Bs.μSS =
    (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ • ∫ p, JF.xiP Bs p • B.rho Bs p H g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho]
  rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

end jd

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_raising_top_of_parts : PBN.RadAATopOfParts := by
  intro hJ hC hM hR hCp Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 y hD F hF
  refine ⟨hCp P.k P.r Wp Wq Bs F y hF, fun Φ hΦ x hx => ?_⟩
  have hL : Q.IsActualLevel X L := hD.2.2.1
  have hc0 : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hγ := Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx

  have e1 : (TL.aP L (y : ℂ)).1 Φ = (L.ζi).1 ((L.Ar (y : ℂ)).1 Φ) := rfl
  rw [e1, hL.2.2.2.2.2.2.2.1]
  show ((X.fn 1 ((L.Ar (y : ℂ)).1 Φ) : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
  rw [X.fn_apply 1 _ x hx, hR P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' X L (y : ℂ) hL Φ x hx]
  have eΦ : Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      Q.crd (Q.vAB P.r (y : ℂ) P.r).1 (Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F)) x.1 x.2 :=
    (vAB_loc (y : ℂ) P.r _ _ (fun c' hc' => hΦ (c', x.2) ⟨hc', hx.2⟩) x.1 hx.1).1
  rw [eΦ, ← hM P.k P.r Wp Wq Bs F (y : ℂ) hF x hx]

  simp only [Q.resG]
  have eJ : B.JF Bs (aaTop Bs y F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) =
      (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)⁻¹ •
        qminorOp (EabH (Hpk P.k P.r)) (C3.xR P.k P.r P.r le_rfl) (C3.xR P.k P.r P.r le_rfl)
          ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) (B.JF Bs F) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) := by
    unfold aaTop
    rw [jf_dinv, hJ P.k P.r Wp Wq Bs F _ hF _ hγ, hC P.k P.r _ _ _ _ _ hx.2.1, hcell.2.2.1, smul_smul]
    congr 1
    rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [eJ, smul_comm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem fpmSh_eq_fpm (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (p₀ : ℕ) :
    fpmSh q f A p₀ = TBBx4.fpm q (fun g => (f g).comp (A g)) (fun _ => ContinuousLinearMap.id ℂ Wq') p₀ := by
  first
  | rfl
  | (unfold fpmSh; rfl)
  | unfold fpmSh

theorem inCC_compSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} {A₀ : ℝ} {d : ℕ} (hf : ∀ m : ℕ, B.InCC A₀ m f) (hA : PolyOp d A) :
    ∀ m : ℕ, B.InCC (A₀ - d) m (fun g => (f g).comp (A g)) := by
  intro m
  have h := shifted_decay P Wp Wq Wq' u u' q f A A₀ d 0 hf hA m
  simp only [mul_zero, Nat.cast_zero, sub_zero] at h
  first
  | exact h
  | (convert h using 2; rw [fpmSh_eq_fpm]; simp [TBBx4.fpm])
  | (convert h using 2; rw [fpmSh_eq_fpm]; unfold TBBx4.fpm)

end sh




end

end Formalism.FourierDecayAlt.P.CutBPEq
end
