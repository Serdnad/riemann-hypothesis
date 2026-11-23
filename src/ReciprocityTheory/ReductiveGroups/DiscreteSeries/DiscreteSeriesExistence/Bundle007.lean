module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle010

@[expose] public section

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := by
    intro k hk x hx
    exact hST.2.1 k (by rw [mir_Kset_eq]; exact hk) x hx
  have hSM : S ≤ (genSub E V).map D.subtype := data_kfin_le hgap hσ hD hV hc hVK S hS hST.1 hSK'
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (hSM hx)
    exact y.2
  obtain ⟨w, hwS, hw0, hwhw⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
    have : y = w := Subtype.ext hyw
    exact this ▸ hy
  have hwV : w ∈ V :=
    khw_lowK_mem hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwG hwhw
  have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (V.map D.subtype) := by
    intro g hg x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    rw [mir_Kset_eq] at hg
    obtain ⟨u, hu, huv⟩ := hVK g hg v hv
    exact Submodule.mem_map.2 ⟨u, hu, by simpa using huv⟩
  have hwT : (w : H) ∈ V.map D.subtype := Submodule.mem_map_of_mem hwV
  have hle : S ≤ V.map D.subtype := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left
        (fun g hg x hx => Submodule.mem_inf.2
          ⟨hST.2.1 g hg x (Submodule.mem_inf.1 hx).1, hTK g hg x (Submodule.mem_inf.1 hx).2⟩) with h | h
    · exfalso
      apply hw0
      have hm : (w : H) ∈ S ⊓ V.map D.subtype := Submodule.mem_inf.2 ⟨hwS, hwT⟩
      rw [h] at hm
      exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
    · rw [← h]
      exact inf_le_right
  rcases (data_isKTypeOf hgap hσ hD hV hc hVK).2.2.1 S hle hST.2.1 with h | h
  · exfalso
    apply hw0
    have hm : (w : H) ∈ S := hwS
    rw [h] at hm
    exact (Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 hm)
  · exact h

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def jSm (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] smD ε (rreg ε) where
  toFun v := ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  map_add' v v' := Subtype.ext (datumEmbedding_add hP v₀ v v')
  map_smul' c v := Subtype.ext (datumEmbedding_smul hP v₀ c v)

theorem jSm_coe (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ((jSm hP v₀ v : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε Ψ v₀ v := rfl

theorem datumV_eq_range (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    datumV ε Ψ v₀ = LinearMap.range (jSm hP v₀) := by
  ext x
  rw [mem_datumV_iff hP v₀ x, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

theorem smE_jSm (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    smE ε (rreg ε) a b (jSm hP v₀ v) = jSm hP v₀ (T.dτ (Matrix.single a b 1) v) :=
  Subtype.ext (rightDerivative_datum_embedding hP v₀ v hab)

theorem jSm_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (jSm hP v₀) := by
  intro v v' h
  apply uniformisationL2_injective hP hv₀
  have := congrArg (fun x : smD ε (rreg ε) => (x : L2 ε)) h
  simpa [jSm_coe] using this

theorem datumV_isKIrrHW (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam) (datumV ε Ψ v₀) := by
  rw [datumV_eq_range hP v₀]
  refine ⟨LinearMap.finiteDimensional_range _, ?_, ?_, ?_⟩
  · rintro a b hab x ⟨v, rfl⟩
    exact ⟨T.dτ (Matrix.single a b 1) v, (smE_jSm hP v₀ v hab).symm⟩
  · intro S' hS' hst
    have hW : ∀ a b, ε a = ε b → ∀ v ∈ S'.comap (jSm hP v₀),
        T.dτ (Matrix.single a b 1) v ∈ S'.comap (jSm hP v₀) := by
      intro a b hab v hv
      rw [Submodule.mem_comap] at hv ⊢
      rw [← smE_jSm hP v₀ v hab]
      exact hst a b hab _ hv
    rcases HW.KType.dτ_irred T _ hW with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := hS' hx
      have hv : v ∈ S'.comap (jSm hP v₀) := hx
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro x ⟨v, rfl⟩
      have hv : v ∈ S'.comap (jSm hP v₀) := by rw [h]; trivial
      exact hv
  · refine ⟨jSm hP v₀ T.w, ⟨T.w, rfl⟩, ?_, ?_, ?_⟩
    · intro h0
      apply HW.KType.w_ne_zero T
      apply jSm_injective hP hv₀
      rw [h0, map_zero]
    · intro a
      rw [smE_jSm hP v₀ T.w rfl, T.w_wt a, map_smul]
    · intro a b _ hab
      rw [smE_jSm hP v₀ T.w hab, T.w_hw a b ‹_› hab, map_zero]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sch_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hne : a ≠ b := hab.ne
  have hΛ : lowK ε (lam - root a b) = lowK ε lam - root a b := by
    unfold lowK; abel
  have hW' : IsKIrrHW ε E (lowK ε (lam - root a b)) W := by rw [hΛ]; exact hW
  have hmono' := ssh_strictAnti hmono hh h2 hE a b hW'
  obtain ⟨z, hzW, -, hz0, hzK⟩ := lowFock_exists ε hE hmono' hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - root a b - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - root a b - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam = 2 - 2 * (lam a - lam b) := by
    rw [sub_add_cancel, ssh_nsq_sub_root lam hne]
    unfold casVal
    ring
  have hgap : h ≤ lam a - lam b := by
    have := hh a b hε
    rwa [abs_of_pos (sub_pos.mpr (hmono hab))] at this
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((2 - 2 * (lam a - lam b) : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  have hneg : (2 - 2 * (lam a - lam b)) < 0 := by linarith
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end
