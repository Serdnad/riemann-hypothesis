module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLAtMost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle092

@[expose] public section

section

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

end hs

section intw

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

def Intw (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (A' : MA.A P (MA.DQ P)) : Prop :=
  ∀ Φ, trR P Bs e (A.1 Φ) = MA.actA P A' (trR P Bs e Φ)

theorem rawR_add (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((Φ + Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ + rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_add, Pi.add_apply, hsv_add, inner_add_right, mul_add]

theorem rawR_smul (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    rawR P Bs.μsec e ((c • Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      c • rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
  funext q
  simp only [rawR, Submodule.coe_smul, Pi.smul_apply, hsv_smul, inner_smul_right, smul_eq_mul]
  ring

theorem toSm_smul' {u : MA.Qp P.r P.TT → ℂ} (c : ℂ) (hu : u ∈ MA.smSub P.r P.TT) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  rw [toSm_of_mem P hu, toSm_of_mem P (Subalgebra.smul_mem _ hu c)]
  rfl

end intw

section clos

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
  {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem trR_add (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (Φ + Ψ) = trR P Bs e Φ + trR P Bs e Ψ := by
  funext ρ
  simp only [trR, Pi.add_apply]
  rw [rawR_add, toSm_add P (hsm Φ ρ) (hsm Ψ ρ)]

theorem trR_smul (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
    (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : trR P Bs e (c • Φ) = c • trR P Bs e Φ := by
  funext ρ
  simp only [trR, Pi.smul_apply]
  rw [rawR_smul, toSm_smul' c (hsm Φ ρ)]

theorem actA_smulM (c : ℂ) (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • x) f = c • MA.actA P x f := by
  funext π
  show ∑ π', ((c • x) π π').1 (f π') = c • ∑ π', (x π π').1 (f π')
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Fintype.sum_eq_single π (fun b hb => by rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl), Matrix.one_apply_eq]
  rfl

theorem actA_alg (c : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) c) f = c • f := by
  rw [Algebra.algebraMap_eq_smul_one, actA_smulM, actA_one]

variable (hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT)
include hsm

theorem intw_add {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A + B) (A' + B') := by
  intro Φ
  show trR P Bs e (A.1 Φ + B.1 Φ) = _
  rw [trR_add hsm, hA, hB, actA_add]

theorem intw_mul {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A * B) (A' * B') := by
  intro Φ
  show trR P Bs e (A.1 (B.1 Φ)) = _
  rw [hA, hB, actA_mul]

theorem intw_alg (c : ℂ) : Intw P Bs e (algebraMap ℂ _ c) (algebraMap ℂ (MA.A P (MA.DQ P)) c) := by
  intro Φ
  show trR P Bs e (c • Φ) = _
  rw [trR_smul hsm, actA_alg]

theorem intw_neg {A : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') : Intw P Bs e (-A) (-A') := by
  have h := intw_mul hsm (intw_alg hsm (-1)) hA
  intro Φ
  have e1 : (-A) = algebraMap ℂ _ (-1) * A := by simp
  have e2 : (-A') = algebraMap ℂ (MA.A P (MA.DQ P)) (-1) * A' := by simp
  rw [e1, e2]
  exact h Φ

theorem intw_sub {A B : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {A' B' : MA.A P (MA.DQ P)}
    (hA : Intw P Bs e A A') (hB : Intw P Bs e B B') : Intw P Bs e (A - B) (A' - B') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact intw_add hsm hA (intw_neg hsm hB)

theorem intw_sum {ι : Type} (s : Finset ι) {A : ι → Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {A' : ι → MA.A P (MA.DQ P)} (h : ∀ i ∈ s, Intw P Bs e (A i) (A' i)) :
    Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  first | exact UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum .. | (apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' h | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A A' | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s A | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι s | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm ι | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e hsm | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs e | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P Bs | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› P | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq ‹_› | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp Wq | exact @UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum Wp

end clos

theorem generator_to_quadratic_form : GenToQQ := by
  intro hRS hGT Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec X
  obtain ⟨d, hL, hstar, hrel, hQQ⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hPl X
  obtain ⟨e, he, hg⟩ := hGT Wp Wq P Bs hPl hk hsec X d hL hstar hrel hQQ
  have hsm : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') ρ,
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈ MA.smSub P.r P.TT :=
    fun Φ ρ => hRS Wp Wq P Bs hPl hk e he Φ ρ
  refine ⟨e, he, fun Φ Y a b => ?_⟩

  have hζ : Intw P Bs e d.L.ζ (MA.zA P (MA.DQ P)) := fun Φ => (hg Φ).1
  have hζb : Intw P Bs e d.L.ζb (MA.zbA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.1
  have hGG : Intw P Bs e d.L.GG (MA.ggA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.1
  have hGGi : Intw P Bs e d.L.GGi (MA.ggiA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.1
  have hnab : Intw P Bs e d.L.nab (MA.nabA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.1
  have hnabs : Intw P Bs e d.L.nabs (MA.nabsA P (MA.DQ P)) := fun Φ => (hg Φ).2.2.2.2.2.2.2.1
  have hκ : ∀ f, Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f) := fun f Φ => (hg Φ).2.2.2.2.2.2.2.2.1 f
  have hSS : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.1 l hl
  have hSSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l)) :=
    fun l hl Φ => (hg Φ).2.2.2.2.2.2.2.2.2.2 l hl

  have hx : Intw P Bs e (d.x Y) (MA.xA P (MA.DQ P) Y) := hκ _
  have hl0 : Intw P Bs e (d.L.l0 Y) (MA.l0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nab - algebraMap ℂ _ (Y + 1/2) * (d.L.ζb * d.L.GGi))
      (-MA.nabA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y + 1 / 2) * (MA.zbA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnab) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζb hGGi))
  have hm0 : Intw P Bs e (d.L.m0 Y) (MA.m0A P (MA.DQ P) Y) := by
    show Intw P Bs e (-d.L.nabs - algebraMap ℂ _ (Y - 1/2) * (d.L.ζ * d.L.GGi))
      (-MA.nabsA P (MA.DQ P) - algebraMap ℂ (MA.A P (MA.DQ P)) (Y - 1 / 2) * (MA.zA P (MA.DQ P) * MA.ggiA P (MA.DQ P)))
    exact intw_sub hsm (intw_neg hsm hnabs) (intw_mul hsm (intw_alg hsm _) (intw_mul hsm hζ hGGi))
  have hS21 : Intw P Bs e (d.weightedSumBis Y) (MA.weightedSumBis P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hSS l hl) (hκ _)
  have hS12 : Intw P Bs e (d.S12 Y) (MA.S12 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_mul hsm (hκ _) (hSSs l hl)
  have hS4 : Intw P Bs e (d.S4 Y) (MA.S4 P (MA.DQ P) Y) :=
    intw_sum hsm _ fun l hl => intw_sum hsm _ fun j hj =>
      intw_mul hsm (intw_mul hsm (hSSs l hl) (hSS j (Finset.mem_of_mem_erase hj))) (hκ _)

  have hent : ∀ a b : Fin 2, Intw P Bs e (d.QQ Y a b) (MA.QQr P (MA.DQ P) Y a b) := by
    intro a b
    fin_cases a <;> fin_cases b
    · show Intw P Bs e (d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
          d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y) (MA.t11 P (MA.DQ P) Y)
      exact intw_add hsm (intw_add hsm (intw_add hsm (intw_add hsm (intw_mul hsm hGGi (hκ _))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hl0))
        (intw_mul hsm (intw_mul hsm (intw_mul hsm hGG hm0) hGGi) hS21))
        (intw_mul hsm hS12 hl0)) (intw_mul hsm hGGi hS4)
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y) (MA.t12 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hm0) hS12
    · show Intw P Bs e (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y) (MA.t21 P (MA.DQ P) Y)
      exact intw_add hsm (intw_mul hsm (intw_mul hsm hGG hx) hl0) hS21
    · show Intw P Bs e (d.L.GG * d.x Y) (MA.t22 P (MA.DQ P) Y)
      exact intw_mul hsm hGG hx
  have ht : X.t Y a b = (X.QQ Y a b).1 := rfl
  rw [ht, hQQ Y]
  exact hent a b Φ

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem sliceLoc_zero : SliceLoc P Bs 0 := by
  intro Φ Φ' c c' _ _ _ ζ _
  simp

theorem sliceLoc_add {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T + S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_smul {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (a : ℂ) (hT : SliceLoc P Bs T) :
    SliceLoc P Bs (a • T) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_mul {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T * S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  exact hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ

theorem sliceLoc_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (hT : ∀ i ∈ s, SliceLoc P Bs (T i)) : SliceLoc P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact sliceLoc_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem sliceLoc_of_smul {T U : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {a : ℂ} (ha : a ≠ 0)
    (hU : U = a • T) (h : SliceLoc P Bs U) : SliceLoc P Bs T := by
  have hTU : T = a⁻¹ • U := by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hTU]
  exact sliceLoc_smul _ h

end closure

open Formalism.FourierDecayAlt.P.NFx4.NO in
theorem second_shift_slice_operator : GTSSLSliceSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl
  have hP := hH.1.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  obtain ⟨Qr, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  have hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1 := by
    intro f Φ Φ' c c' hc hc' h ζ hζ
    have e1 := hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩
    have e2 := hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩
    simp only at e1 e2
    rw [e1, e2, h ζ hζ]
  have hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1 := fun ρ => hK _
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  refine ⟨?_, ?_⟩
  · have hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (d.SS l))

      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1 := by
        have h := congrArg (fstA _) (B1 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e10]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))
    · rw [block_zero hRel hUp]
      exact sliceLoc_zero
  · have hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (star (d.SS l)))

      simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1 := by
        have h := congrArg (fstA _) (B4 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e01]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))
    · rw [star_block_zero hRel hUp]
      exact sliceLoc_zero

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep in
theorem gauge_left_line_holds : GLLeft := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk ζ hζ Fr hFr
  obtain ⟨-, hz, hz', hTz, hTz', -, -⟩ := hpl
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set μ := NF.muZ P.k P.r Bs.μsec ζ with hμ
  have hm := NFRadRedA.muZ_uwb Bs.sec hζ'
  have hG := NFRadRedA.uwb_glev hm
  have hU : μ ∈ UH (Hpk P.k P.r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hUi : μ⁻¹ ∈ UH (Hpk P.k P.r) := hGi.1
  have hT := Bs.T_pos

  set y := μ *ᵥ Bs.z' with hydef
  have hy : inWb P.k P.r y := Qx8.inWb_mulVec hG hz'
  have hyz : herm (Hpk P.k P.r) y Bs.z = ζ := by
    rw [← NFRadRedA.zeta_eq]; exact NFRadRedA.zeta_muZ hz hz' Bs.sec hζ'
  have hyy : herm (Hpk P.k P.r) y y = -((Tz P.k P.r Bs.z' : ℝ) : ℂ) := by
    rw [Qx2.herm_uh hU, FrameEntries.herm_self]
  have hpos : 0 < Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [sub_pos, lt_div_iff₀ hT]; linarith
  set p := SSn.prWv P.k P.r Bs.z y with hpdef
  have hpp := DU.prWv_norm hT hy hyy hyz
  have hre : (herm (Hpk P.k P.r) p p).re = Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z' := by
    rw [hpp]; simp
  have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ =
      (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) • p := by
    show SSn.unitH P.k P.r p = _
    unfold SSn.unitH
    rw [hre]
  have hsne : (((Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z'))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Complex.normSq ζ / Tz P.k P.r Bs.z - Tz P.k P.r Bs.z') := Real.sqrt_pos.2 hpos
    exact_mod_cast (inv_pos.2 this).ne'

  have hFz : ∀ a, herm (Hpk P.k P.r) (Fr a) Bs.z = 0 := fun a => hFr.2.2 a Bs.z (by simp)
  have hFy : ∀ a, herm (Hpk P.k P.r) (Fr a) y = 0 := by
    intro a
    have h1 : herm (Hpk P.k P.r) (Fr a) (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 := hFr.2.2 a _ (by simp)
    rw [hν, DU.hsmul_r] at h1
    have h2 : herm (Hpk P.k P.r) (Fr a) p = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) hsne
      · exact h
    rw [hpdef, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hFz a, mul_zero, add_zero] at h2
    exact h2
  have hmi : μ⁻¹ * μ = 1 := Gauge.GC.KLAM.inv_mul_uh hU
  have hmm : μ * μ⁻¹ = 1 := Gauge.GC.KLAM.mul_inv_uh hU
  have hz'e : Bs.z' = μ⁻¹ *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hF' : Q.IsFrameOf P.k P.r [μ⁻¹ *ᵥ Bs.z, Bs.z'] (fun a => μ⁻¹ *ᵥ Fr a) := by
    refine ⟨fun a => Qx8.inWb_mulVec hGi (hFr.1 a), fun a b => ?_, fun a w hw => ?_⟩
    · rw [Qx2.herm_uh hUi]; exact hFr.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rw [Qx2.herm_uh hUi]; exact hFz a
      · rw [hz'e, Qx2.herm_uh hUi]; exact hFy a
  refine ⟨hF', fun X hX w v => ?_⟩
  have hXF : X ∈ Gauge.GC.FibAt P.k P.r Bs.z Bs.z' Bs.π Bs.π' μ :=
    fun h hh h' hh' he => hX (h, h') ⟨hh, hh', he⟩
  have hint := Qx8.capRep_intertwine hF' Bs.π'_rep Bs.π'_cont hU X
    (fun h' hh' hy' u => Gauge.GC.KLAM.fib_intertwine Bs.π_rep hG hXF hh' hy' u) w v
  have hback : (fun a => μ *ᵥ (μ⁻¹ *ᵥ Fr a)) = Fr := by
    funext a
    rw [Matrix.mulVec_mulVec, hmm, Matrix.one_mulVec]
  rw [hint, hback]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho.GL
end
