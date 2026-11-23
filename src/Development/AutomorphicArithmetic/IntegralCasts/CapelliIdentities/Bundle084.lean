module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.IntertwinerStructure.Intw :
    {Wp Wq : Type} →
      [inst : NormedAddCommGroup Wp] →
        [inst_1 : InnerProductSpace ℂ Wp] →
          [inst_2 : NormedAddCommGroup Wq] →
            [inst_3 : InnerProductSpace ℂ Wq] →
              [FiniteDimensional ℂ Wq] →
                (P : Formalism.FourierDecayAlt.M.Par) →
                  (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) →
                    (Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) →
                      Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') →
                        Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P) → Prop :=
    fun {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
        [FiniteDimensional ℂ Wq] (P : Formalism.FourierDecayAlt.M.Par) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq)
        (e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) (A : Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
        (A' : Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)) ↦
      ∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
        Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e
                  ((A.1 : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
                    Φ) =
          Formalism.FourierDecayAlt.MA.actA P A' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ)

theorem UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum :
    ∀ {Wp Wq : Type} [inst : NormedAddCommGroup Wp] [inst_1 : InnerProductSpace ℂ Wp] [inst_2 : NormedAddCommGroup Wq]
      [inst_3 : InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [inst_5 : FiniteDimensional ℂ Wq] {P : Formalism.FourierDecayAlt.M.Par}
      {Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq} {e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp},
      (∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (ρ : Formalism.FourierDecayAlt.M.Ty P),
          Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e (↑Φ : Formalism.FourierDecayAlt.Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈
            Formalism.FourierDecayAlt.MA.smSub P.r P.TT) →
        ∀ {ι : Type} (s : Finset ι) {A : ι → Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
          {A' : ι → Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)},
          (∀ i ∈ s, UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (A i) (A' i)) → UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hs ι s A A' h
  have hv : ∀ Φ ρ q, (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ ρ).1 q =
      Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e Φ.1 ρ q := fun Φ ρ q => by
    simp only [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR, Formalism.FourierDecayAlt.MA.toSm, dif_pos (hs Φ ρ)]
  have hh : ∀ X Y : Wq →L[ℂ] Wp, Formalism.FourierDecayAlt.B.hsVec (X + Y) = Formalism.FourierDecayAlt.B.hsVec X + Formalism.FourierDecayAlt.B.hsVec Y := fun _ _ => rfl
  let T : _ →+ _ := AddMonoidHom.mk' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e) fun Φ Ψ => funext fun ρ => Subtype.ext <|
    funext fun q => (hv _ ρ q).trans <| Eq.trans (by simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR, hh, inner_add_right, mul_add])
      (congrArg₂ (· + ·) (hv Φ ρ q) (hv Ψ ρ q)).symm
  refine Finset.sum_induction (p := fun x : _ × _ => UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e x.1 x.2) (fun i => (A i, A' i))
    (fun a b ha hb Φ => (T.map_add _ _).trans ((congrArg₂ (· + ·) (ha Φ) (hb Φ)).trans
      (funext fun ρ => Finset.sum_add_distrib.symm)))
    (fun Φ => T.map_zero.trans (funext fun ρ => Finset.sum_const_zero.symm)) h |> fun H => ?_
  simpa only [Prod.fst_sum, Prod.snd_sum] using H
end

section

attribute [local instance] Submodule.module._proof_1 Formalism.MainNotions.S.lf._proof_1 Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul :
    ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E}
    (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (M : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.WbQ D F0)),
    Submodule.span D.host.E (↑M : Set (Formalism.MainNotions.S.WbQ D F0)) = ⊤ →
      ∀ (m : Formalism.MainNotions.S.WbQ D F0),
        ∃ (k : ℕ),
          k ≠ (0 : ℕ) ∧
            (↑k : NumberField.RingOfIntegers D.host.E) • m ∈
              M := by
  intro D T F0 M h m
  simp only [Nat.cast_smul_eq_nsmul]
  refine Submodule.span_induction (p := fun x _ => ∃ k : ℕ, k ≠ 0 ∧ k • x ∈ M)
    (fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h ▸ Submodule.mem_top : m ∈ Submodule.span D.host.E (M : Set _))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    exact ⟨a * b, mul_ne_zero ha hb, by
      rw [smul_add, mul_nsmul' y, mul_nsmul x]; exact M.add_mem (nsmul_mem hx b) (nsmul_mem hy a)⟩
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨b, s, hb, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic c)).exists_nsmul_eq (NumberField.RingOfIntegers D.host.E)
    exact ⟨b * a, mul_ne_zero hb ha, by
      rw [mul_smul, smul_comm a c, ← smul_assoc, hs, algebraMap_smul]; exact M.smul_mem s hx⟩
end
