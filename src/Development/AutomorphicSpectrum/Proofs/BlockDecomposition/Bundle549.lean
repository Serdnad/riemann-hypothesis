module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvaluationOfMemAdjoin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle474
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicStandardTournament
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle527
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryModelHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle526
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.InvPickKP

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.RealMult (Pair2 Inv2 ev2)

variable {n : ℕ}

def toKP : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p =>
    if p.1 then (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) + FreeAlgebra.ι ℂ (true, p.2))
    else (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, p.2) - FreeAlgebra.ι ℂ (true, p.2))

theorem evalCartan_toCartan {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : evKP E1 E2 (toKP a) = ev2 E1 E2 a := by
  have eK : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E1 a b + E2 a b := fun a b => by
    simp [evKP, kA]
  have eP : ∀ a b, evKP E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b - E2 a b := fun a b => by
    simp [evKP, pA]
  have h : (evKP E1 E2).comp toKP = ev2 E1 E2 := by
    apply FreeAlgebra.hom_ext
    funext ⟨s, a, b⟩
    show evKP E1 E2 (toKP (FreeAlgebra.ι ℂ (s, a, b))) = ev2 E1 E2 (FreeAlgebra.ι ℂ (s, a, b))
    cases s
    · have t : toKP (FreeAlgebra.ι ℂ (false, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) - FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (false, a, b)) = E2 a b := by simp [ev2]
      rw [t, e, map_smul, map_sub, eK, eP]
      module
    · have t : toKP (FreeAlgebra.ι ℂ (true, a, b)) =
          (1 / 2 : ℂ) • (FreeAlgebra.ι ℂ (false, a, b) + FreeAlgebra.ι ℂ (true, a, b)) := by simp [toKP]
      have e : ev2 E1 E2 (FreeAlgebra.ι ℂ (true, a, b)) = E1 a b := by simp [ev2]
      rw [t, e, map_smul, map_add (f := _), eK, eP]
      module
  exact DFunLike.congr_fun h a

theorem invKP_toKP {a : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (h : Inv2 a) : InvKP n (toKP a) := by
  intro V _ _ E1 E2 hE c d
  rw [evalCartan_toCartan]
  exact h V E1 E2 ⟨hE.1, hE.2.1, hE.2.2⟩ c d

theorem invPick : InvPick := by
  intro n lam lev V _ _ E1 E2 hA μ v w hv hw hv0 hx
  obtain ⟨a, ha, hav⟩ := GlobalTheory.CompanionTheory.RealMult.Lift.liftInv n V E1 E2 ⟨hA.gl1, hA.gl2, hA.comm⟩ hA.unitK hA.locFin
    μ v w hv0 hv hw hx
  exact ⟨toKP a, invKP_toKP ha, by rw [evalCartan_toCartan, hav]⟩

end GlobalTheory.CompanionTheory.InvPickKP
end
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.real_compression : PositivityTheory.RgBcC.RealD.Compress := by
  first | exact @GlobalTheory.CompanionTheory.LevelCompress.exists_compress | exact GlobalTheory.CompanionTheory.LevelCompress.exists_compress | (intros; apply GlobalTheory.CompanionTheory.LevelCompress.exists_compress <;> assumption)
end

section

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes

variable {n : ℕ}

theorem wtB_union {S T : Finset (Fin n × Fin n)} (h : Disjoint S T) : wtB (S ∪ T) = wtB S + wtB T := by
  funext c
  simp only [wtB, Pi.add_apply, Finset.filter_union]
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
  push_cast
  ring

theorem wtB_sdiff {S T : Finset (Fin n × Fin n)} (h : T ⊆ S) : wtB (S \ T) = wtB S - wtB T := by
  have h1 : wtB (S \ T ∪ T) = wtB (S \ T) + wtB T :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset h] at h1
  rw [h1, add_sub_cancel_right]

theorem wtB_lev (lev : Fin n → ℕ) :
    wtB (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) = fun c => 2 * rhoU lev c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev c < lev b).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)).card
      = (univ.filter fun b : Fin n => lev b < lev c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    exact Finset.filter_congr (fun b _ => by simp)
  simp only [wtB, rhoU, e1, e2]
  ring

theorem wtB_pos :
    wtB (univ.filter fun p : Fin n × Fin n => p.1 < p.2) = fun c => 2 * rhoV n c := by
  funext c
  have e1 : (Finset.filter (fun p : Fin n × Fin n => p.1 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Ioi c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_fst]
    congr 1
    ext b
    simp
  have e2 : (Finset.filter (fun p : Fin n × Fin n => p.2 = c)
      (univ.filter fun p : Fin n × Fin n => p.1 < p.2)).card = (Finset.Iio c).card := by
    rw [GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.card_snd]
    congr 1
    ext b
    simp
  have hc : (c : ℕ) < n := c.isLt
  simp only [wtB, rhoV, e1, e2, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.cast_sub (by omega : (c : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem domC_eq {y z : Fin n → ℝ} (hz : StrictAnti z) {w : Equiv.Perm (Fin n)} (h : z = y ∘ w) : domC y = z := by
  subst h
  have hm : Monotone ((fun a => -y a) ∘ ⇑w) := by
    intro a b hab
    have := hz.antitone hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  have key := (Tuple.comp_sort_eq_comp_iff_monotone (f := fun a => -y a) (σ := w)).mpr hm
  funext a
  have ha := congrFun key a
  simp only [Function.comp_apply, neg_inj] at ha
  simp only [domC, Function.comp_apply]
  exact ha.symm

theorem nsq_eq (x : Fin n → ℝ) : PositivityTheory.RgBcC.RealD.nsq x = Formalism.REAL.nsq x := by
  simp [PositivityTheory.RgBcC.RealD.nsq, Formalism.REAL.nsq, Formalism.REAL.dot, sq]

theorem mem_topTypes {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {ν : Fin n → ℝ}
    (h : IsSecondTypeWeight lam lev ν) : ν ∈ topTypes lam := by
  have hmono : Monotone lev := by
    unfold PositivityTheory.RgBcC.RealD.IsLev at hl
    exact hl.1
  unfold PositivityTheory.RgBcC.RealD.IsSecondTypeWeight at h
  obtain ⟨B, _hB, hBlev, hanti, w, hw⟩ := h
  have hLP : (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)
      ⊆ (univ.filter fun p : Fin n × Fin n => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hmono.reflect_lt hp
  have hBL : B ⊆ (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hBlev p hp
  have hdisj : Disjoint ((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) B :=
    Finset.sdiff_disjoint.mono_right hBL
  have hid : muQ lam lev + rhoV n - wtB B =
      (fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B) := by
    rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_union hdisj, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_sdiff hLP,
      GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_pos, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.wtB_lev]
    funext a
    simp only [muQ, Pi.add_apply, Pi.sub_apply]
    ring
  have hdom : domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n -
        wtB (((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
          (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B)) = ν + rhoV n :=
    GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.domC_eq (w := w) hanti (by rw [hw, hid])
  unfold PositivityTheory.RgBcC.RealD.topTypes
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨((univ.filter fun p : Fin n × Fin n => p.1 < p.2) \
      (univ.filter fun p : Fin n × Fin n => lev p.1 < lev p.2)) ∪ B, ?_, ?_⟩, hanti⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro p hp
    rcases Finset.mem_union.mp hp with h1 | h1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2
    · exact hmono.reflect_lt (hBlev p h1)
  · simp only [hdom, add_sub_cancel_right]

theorem n2T : PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter := by
  unfold PositivityTheory.RgBcC.RealD.SecondTypeWeightsShorter
  intro m lam hlam lev hl ν h
  refine ⟨GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.mem_topTypes hl h, ?_⟩
  rw [GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq, GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.nsq_eq]
  exact GlobalTheory.CompanionTheory.MultOne.ShortSecondWeights.nsq_lt m lam hlam lev hl ν h

end GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes
end
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC.RealD
theorem _root_.GlobalTheory.T.derivative_unitary_action : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  exact @GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.diagonal_algebra_holds : DiagAlg := by
  first | exact @GlobalTheory.CompanionTheory.BlockScalars.diagAlg | exact GlobalTheory.CompanionTheory.BlockScalars.diagAlg | (intros; apply GlobalTheory.CompanionTheory.BlockScalars.diagAlg <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.spectral_trace_of_model_algebra : UModel → LocAlg → SpecTrace := by
  first | exact @GlobalTheory.CompanionTheory.SpecModel.specTrace | exact GlobalTheory.CompanionTheory.SpecModel.specTrace | (intros; apply GlobalTheory.CompanionTheory.SpecModel.specTrace <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.split_dictionary_holds : SplitDict := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlace.splitDict | exact GlobalTheory.CompanionTheory.SplitPlace.splitDict | (intros; apply GlobalTheory.CompanionTheory.SplitPlace.splitDict <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.local_algebra_holds : LocAlg := by
  first | exact @GlobalTheory.CompanionTheory.LocHecke.locAlg | exact GlobalTheory.CompanionTheory.LocHecke.locAlg | (intros; apply GlobalTheory.CompanionTheory.LocHecke.locAlg <;> assumption)
end

section

open PositivityTheory.Rg.BcB.F.Eig

theorem _root_.GlobalTheory.T.unitary_model_holds : UModel := by
  first | exact @GlobalTheory.CompanionTheory.UMod.uModel | exact GlobalTheory.CompanionTheory.UMod.uModel | (intros; apply GlobalTheory.CompanionTheory.UMod.uModel <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Function
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitaryWord

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.U

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev unitFn (n : ℕ) (w : Pl E) : UL n w → ℂ := (KL n w : Set (UL n w)).indicator 1

theorem isHecke_zero {w : Pl E} (K' : Subgroup (UL n w)) : IsHecke K' (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isHecke_lone (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    IsHecke K' (lone K') :=
  (hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1

theorem isHecke_lconv (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {f₁ f₂ : UL n w → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) : IsHecke K' (lconv f₁ f₂) :=
  (hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1

theorem lone_KL (w : Pl E) : lone (KL n w) = unitFn n w := by
  simp [lone, unitFn, Subgroup.relIndex_self]
  rfl

theorem isHecke_lpow (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (lpow K' g k) := by
  induction k with
  | zero => exact isHecke_lone hL hK
  | succ k ih => exact isHecke_lconv hL hK hg ih

section Fam

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  (F : UFam S lam K') {B : Finset (Pl E)}

end Fam

end GlobalTheory.CompanionTheory.UnitaryWord

end
end

section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

theorem _root_.GlobalTheory.T.torus_exponent_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  first | exact @GlobalTheory.CompanionTheory.TorusExpU.torusExp | exact GlobalTheory.CompanionTheory.TorusExpU.torusExp | (intros; apply GlobalTheory.CompanionTheory.TorusExpU.torusExp <;> assumption)
end PExp
end Tail
end F
end BcB
end Rg
end PositivityTheory
end

section

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.LocalThetaTranslation

theorem phi_transpose (n : ℕ) (R : Type) [CommRing R] :
    (GlobalTheory.Tw.Phi n R)ᵀ = ((-1 : R) ^ (n + 1)) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · have h' : (j : ℕ) + i + 1 = n := by omega
    rw [if_pos h, if_pos h', ← pow_add]
    have e : n + 1 + (i : ℕ) = j + 2 * ((i : ℕ) + 1) := by omega
    rw [e, pow_add, pow_mul]
    simp
  · have h' : ¬ (j : ℕ) + i + 1 = n := by omega
    rw [if_neg h, if_neg h']
    simp

theorem phi_map (n : ℕ) {R : Type} [CommRing R] (c : R →+* R) : (GlobalTheory.Tw.Phi n R).map c = GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (n : ℕ) (R : Type) [CommRing R] :
    GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h := Phi_mul_transpose n R
  rw [phi_transpose, Matrix.mul_smul] at h
  have e : ((-1 : R) ^ (n + 1)) * ((-1 : R) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; simp
  rw [← h, smul_smul, e, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_conj_eq_sign (n : ℕ) : ∃ s : E, s ≠ 0 ∧ conjE E s = (-1 : E) ^ (n + 1) * s := by
  rcases neg_one_pow_eq_or E (n + 1) with h | h
  · exact ⟨1, one_ne_zero, by rw [h, map_one, one_mul]⟩
  · have hx : ∃ x : E, conjE E x ≠ x := by
      by_contra hc
      push Not at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    have hcc : conjE E (conjE E x) = x := IsCMField.complexConj_apply_apply E x
    refine ⟨x - conjE E x, sub_ne_zero.2 hx.symm, ?_⟩
    rw [h, map_sub, hcc]
    ring


omit [NumberField E] [IsCMField E] in
theorem scalar_val {n : ℕ} (t : Eˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h]


omit [NumberField E] [IsCMField E] in
theorem scalar_commute {n : ℕ} (t : Eˣ) (g : GL (Fin n) E) :
    GeneralLinearGroup.scalar (Fin n) t * g = g * GeneralLinearGroup.scalar (Fin n) t := by
  apply Units.ext
  simp only [Units.val_mul, scalar_val]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem thetaE_phiU (n : ℕ) : (thetaE E n (PhiU n E)).val = GlobalTheory.Tw.Phi n E := by
  change ((((PhiU n E)⁻¹).val).map (conjE E))ᵀ = _
  rw [phiU_inv_val, Matrix.transpose_map, Matrix.transpose_transpose, phi_map]

theorem thetaE_scalar {n : ℕ} (t : Eˣ) :
    (thetaE E n (GeneralLinearGroup.scalar (Fin n) t)).val =
      (conjE E (t : E))⁻¹ • (1 : Matrix (Fin n) (Fin n) E) := by
  change ((((GeneralLinearGroup.scalar (Fin n) t)⁻¹).val).map (conjE E))ᵀ = _
  rw [← map_inv, scalar_val]
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem translEx : TranslEx := by
  intro E _ _ _ n
  obtain ⟨s, hs, hc⟩ := exists_conj_eq_sign (E := E) n
  have hcs : conjE E s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hs
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E, ?_, ?_⟩
  · intro g
    have h1 : thE E n g = PhiU n E * thetaE E n g * (PhiU n E)⁻¹ := thetaGL_eq n E _ g
    rw [h1]
    have h2 := scalar_commute (Units.mk0 s hs) (PhiU n E * thetaE E n g * (PhiU n E)⁻¹)
    have h3 : GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E * thetaE E n g *
        (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * (PhiU n E * thetaE E n g * (PhiU n E)⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs))⁻¹ := by
      group
    rw [h3, h2, mul_inv_cancel_right]
  · apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_mul, Units.val_mul, thetaE_phiU, thetaE_scalar, scalar_val, phiU_val]
    simp only [Units.val_mk0, Units.val_one]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      phi_mul_self, smul_smul, smul_smul, hc]
    have hp : ((-1 : E) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have : s * (((-1 : E) ^ (n + 1)) * s)⁻¹ * ((-1 : E) ^ (n + 1)) = 1 := by
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.LocalThetaTranslation
end
end
