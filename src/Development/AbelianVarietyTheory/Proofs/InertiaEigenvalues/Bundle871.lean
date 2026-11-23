module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle709
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle858
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle860
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle861
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.exists_places_thetaFunction_fixedVectorShape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f := by
  first | exact @GlobalTheory.DownLift.ShapeOff.exists_likeOff | exact GlobalTheory.DownLift.ShapeOff.exists_likeOff | (intros; apply GlobalTheory.DownLift.ShapeOff.exists_likeOff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar

variable {D : D7}

theorem isHalf_add {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_neg {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := fun i j => by
  simp only [Matrix.neg_apply, mul_neg, hu i j]

theorem isHalf_sub {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hu (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hv)

theorem isHalf_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem isHalf_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun i j => by
  simp only [Matrix.zero_apply, mul_zero]

theorem isHalf_place_of_left {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + cA D a) u := fun i j => by
  have h : cA D a * u i j = 0 := by rw [← hu i j, ← mul_assoc, mul_comm (cA D a) a, ha, zero_mul]
  rw [add_mul, h, add_zero, hu i j]

theorem isHalf_place_of_right {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n}
    (hu : IsHalf (cA D a) u) : IsHalf (a + cA D a) u := fun i j => by
  have h : a * u i j = 0 := by rw [← hu i j, ← mul_assoc, ha, zero_mul]
  rw [add_mul, h, zero_add, hu i j]

theorem heisO_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ)
    {h : WO S T → ℂ} (hh : h ∈ locSpan ψ S T a f) {w : WO S T} (hw : IsHalf (a + cA D a) w) :
    heisO ψ S T w h ∈ locSpan ψ S T a f := by
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, hu, rfl⟩ := hp
    rw [heisO_heisO]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + u, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hw hu, rfl⟩)
  | zero =>
    rw [show heisO ψ S T w 0 = 0 from (heisL ψ S T w).map_zero]
    exact Submodule.zero_mem _
  | add p q _ _ hp hq =>
    rw [show heisO ψ S T w (p + q) = heisO ψ S T w p + heisO ψ S T w q from (heisL ψ S T w).map_add p q]
    exact Submodule.add_mem _ hp hq
  | smul c p _ hp =>
    rw [heisO_smul]
    exact Submodule.smul_mem _ _ hp

theorem self_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) :
    f ∈ locSpan ψ S T a f :=
  Submodule.subset_span ⟨0, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_zero _, (heisO_zero ψ S T f).symm⟩

end GlobalTheory.DownLift.SplitCoef.Cons


open GlobalTheory.SplitScalar GlobalTheory.DownLift.SplitCoef.Cons in
theorem GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : WO S T → ℂ, IsSBHalf a (latH S T ΛS ΛT) Φ → ∀ x₁, IsHalf a x₁ → ∃ f' ∈ locSpan ψ S T a f, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f') = Φ x * ℓ (heisO ψ S T x₁ f) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf Φ hΦ x₁ hx₁
  classical
  obtain ⟨⟨k₀, hk₀, hinv, hsupp⟩, -, -⟩ := GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ ΛS ΛT hS hT a ha f hf
  obtain ⟨hΦs, kΦ, hkΦ, hΦinv, hΦsupp⟩ := hΦ
  obtain ⟨k₁, hk₁, hx₁Λ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) x₁ (half_fin ha hx₁)
  obtain ⟨k, hk, hfix, hΦk, hkx₁, hk0, hkΦ'⟩ : ∃ k : ℕ, 0 < k ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → heisO ψ S T (k • u) f = f) ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → ∀ t, Φ (t + k • u) = Φ t) ∧
      k • x₁ ∈ latH S T ΛS ΛT ∧
      (∀ y, k₀ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) ∧
      (∀ y, kΦ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) := by
    refine ⟨k₀ * kΦ * k₁, by positivity, fun u hu hua => ?_, fun u hu hua t => ?_, ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · rw [mul_assoc, mul_smul]
      exact hinv _ (AddSubgroup.nsmul_mem _ hu _) (Or.inl (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _))
    · rw [show k₀ * kΦ * k₁ = kΦ * (k₀ * k₁) by ring, mul_smul]
      exact hΦinv _ (AddSubgroup.nsmul_mem _ hu _) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _) t
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ hx₁Λ _
    · rw [show k₀ * kΦ * k₁ = (kΦ * k₁) * k₀ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
    · rw [show k₀ * kΦ * k₁ = (k₀ * k₁) * kΦ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
  have hca : IsSplitIdem D (cA D a) := isSplitIdem_conj ha
  have hcaa : cA D a * a = 0 := by rw [mul_comm]; exact ha.2.1
  obtain ⟨Y, hYne, hY, -, hYsum⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, -, hX, hXu, -⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT (cA D a) hca.1 (infPart_splitIdem hca) k hk
  simp only [GlobalTheory.DualPairCheck.cA_cA] at hX hXu
  obtain ⟨n, hn⟩ : ∃ n, n = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x₁ f) := ⟨_, rfl⟩

  have hA : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x n) =
      if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f) else 0 := by
    intro ℓ hℓ x hx
    have hg : IsThetaFunO ψ S T (heisO ψ S T x₁ f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x₁
    have hxg : IsThetaFunO ψ S T (heisO ψ S T x (heisO ψ S T x₁ f)) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg x
    have h1 : ℓ (heisO ψ S T x n) =
        (∑ y ∈ Y, ψ (symplO S T x y)) * ℓ (heisO ψ S T x (heisO ψ S T x₁ f)) := by

      rw [hn, heisO_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [heisO_comm, ℓ.map_smul, smul_eq_mul, hℓ y (hY y hy).1 _ hxg]
    have h2 : heisO ψ S T x (heisO ψ S T x₁ f) = heisO ψ S T (x + x₁) f :=
      (heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx hx₁) f).symm
    rw [h1, h2]
    split_ifs with hP
    · obtain ⟨u, hu, hua, rfl⟩ := hP
      have hkx : k • (k • u) ∈ latH S T ΛS ΛT := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hu _) _
      rw [Finset.sum_congr rfl fun y hy => (hYsum (k • u) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k) hkx).1 ⟨u, hu, hua, rfl⟩ y hy,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have horth : symplO S T x₁ (k • u) = 0 := symplO_eq_zero S T hcaa hx₁ (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k)
      rw [add_comm, heisO_add_of_orth ψ S T horth f, hfix u hu hua]
    · by_cases hkx : k • x ∈ latH S T ΛS ΛT
      · rw [(hYsum x hx hkx).2 hP, zero_mul]
      · have h3 : ℓ (heisO ψ S T (x + x₁) f) = 0 := by
          by_contra hne
          apply hkx
          have h4 := hk0 _ (hsupp ℓ hℓ (x + x₁) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hx hx₁) hne)
          have h5 : k • x = k • (x + x₁) - k • x₁ := by rw [nsmul_add, add_sub_cancel_right]
          rw [h5]
          exact AddSubgroup.sub_mem _ h4 hkx₁
        rw [h3, mul_zero]
  refine ⟨((Y.card : ℂ)⁻¹) • ∑ z ∈ X, Φ z • heisO ψ S T (-z) n, ?_, ?_⟩
  · have hg : heisO ψ S T x₁ f ∈ locSpan ψ S T a f :=
      heisO_mem_locSpan ψ S T a f (self_mem_locSpan ψ S T a f) (isHalf_place_of_left ha.2.1 hx₁)
    have hnm : n ∈ locSpan ψ S T a f := by
      rw [hn]
      exact Submodule.sum_mem _ fun y hy =>
        heisO_mem_locSpan ψ S T a f hg (isHalf_place_of_right ha.2.1 (hY y hy).1)
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _
      (heisO_mem_locSpan ψ S T a f hnm (isHalf_place_of_left ha.2.1 (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg (hX z hz).1))))
  · intro ℓ hℓ x hx
    have hc : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hYne.card_pos.ne'

    rw [heisO_smul, heisO_sum, ℓ.map_smul, map_sum, smul_eq_mul]
    have hterm : ∀ z ∈ X, ℓ (heisO ψ S T x (Φ z • heisO ψ S T (-z) n)) = Φ x *
        (if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x - z = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f)
          else 0) := by
      intro z hz
      have hzh := (hX z hz).1
      rw [heisO_smul, ℓ.map_smul, smul_eq_mul,
        ← heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hzh)) n, ← sub_eq_add_neg,
        hA ℓ hℓ (x - z) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_sub hx hzh)]
      split_ifs with hP
      · obtain ⟨u, hu, hua, hxu⟩ := hP
        rw [(sub_eq_iff_eq_add').1 hxu, hΦk u hu hua]
      · rw [mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    by_cases hΦx : Φ x = 0
    · rw [hΦx, zero_mul, mul_zero, zero_mul]
    · obtain ⟨z₀, ⟨hz₀, hP₀⟩, huniq⟩ := hXu x hx (hkΦ' x (hΦsupp x hΦx))
      rw [Finset.sum_eq_single_of_mem z₀ hz₀ (fun z hz hne => if_neg fun hP => hne (huniq z ⟨hz, hP⟩)),
        if_pos hP₀]
      field_simp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  first | exact @GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | exact GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform | (intros; apply GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead


namespace GlobalTheory.MtReadRat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (σA : A →+* A) (σB : B →+* B)
    (hc : ∀ x, φ (σA x) = σB (φ x)) {m : Type} [Fintype m] [DecidableEq m] (J g : Matrix m m A) :
    Formalism.UG.cT σB (g.map φ) * J.map φ * g.map φ = (Formalism.UG.cT σA g * J * g).map φ := by
  have : Formalism.UG.cT σB (g.map φ) = (Formalism.UG.cT σA g).map φ := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [this, Matrix.map_mul, Matrix.map_mul]

variable {D : D7}

theorem finHom_entry (V : HSp D) (h : GA D V) (X : GL (Fin V.rank) D.host.E) (hX : matHom V h = Formalism.UG.bc (incA D) X)
    (a b : Fin V.rank) : (finHom V h).1 a b = inclR (F := D.host.F) (Af D.host.F) (X.1 a b) := by
  have : (finHom V h).1 a b = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V h).1 a b) := rfl
  rw [this, hX]
  simp [Formalism.UG.bc, inclR, incA]

theorem entry_of_ratF {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b))
    (κ : GAf D.host.E V.rank) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E)
    (e : Bridge.ratF V γ' = frameEquiv P κ) (hR : Bridge.IsRatMat V γ' γE) (a c : Fin V.rank) :
    ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a c =
      Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  have e' : finHom V γ'.1 = finHom V (P.ψ κ) := congrArg Subtype.val e
  have h1 := hId κ a c
  have h2 : finMat D.sp.cm.sig V.gram (P.ψ κ) a c = inclR (F := D.host.F) (Af D.host.F) (γE.val a c) := by
    show (finHom V (P.ψ κ)).1 a c = _
    rw [← e']
    exact finHom_entry V γ'.1 γE hR a c
  rw [h2] at h1
  rw [← (RingEquiv.eq_symm_apply _).1 h1]
  exact GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _

theorem ratMatch_fwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) :
    ∃ γ' : Formalism.L2.Theta.GQ V, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γ0, hγ0, e0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hγent : ∀ a b, (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b =
      Algebra.TensorProduct.includeLeftRingHom ((γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun a b => by
    rw [← e0]; exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have hfin : ∀ a b, (finHom V (P.ψ γ.1)).1 a b = inclR (F := D.host.F) (Af D.host.F) ((γ0 : Matrix _ _ D.host.E) a b) :=
    fun a b => by
      show finMat D.sp.cm.sig V.gram (P.ψ γ.1) a b = _
      rw [hId]
      simp only [Fin.cast_eq_self]
      rw [hγent, RingEquiv.symm_apply_eq]
      exact (GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _).symm

  have hsnd : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (sigR (AF D.host.F) D.sp.cm.sig x) =
      sigR (Af D.host.F) D.sp.cm.sig ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom x) :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hUA := (P.ψ γ.1).2
  change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((P.ψ γ.1).1.1) * JR (AF D.host.F) V.gram * (P.ψ γ.1).1.1 =
    JR (AF D.host.F) V.gram at hUA
  have hUf := congrArg (fun M => M.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) hUA
  rw [← cT_map _ _ _ hsnd] at hUf
  have hM : ((P.ψ γ.1).1.1 : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      (γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; exact hfin a b
  have hJ : (JR (AF D.host.F) V.gram).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      V.gram.map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; simp [JR, inclR]
  have hci : ∀ (R : Type) [CommRing R] [Algebra D.host.F R] (x : D.host.E),
      inclR (F := D.host.F) R (D.sp.cm.sig x) = sigR R D.sp.cm.sig (inclR (F := D.host.F) R x) := fun R _ _ x => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rw [hM, hJ, cT_map _ _ _ (hci (Af D.host.F))] at hUf
  have hγ0' : γ0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := Matrix.map_injective hinjR hUf
  have hHR : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ0 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * (γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [JR, cT_map _ _ _ (hci (AF D.host.F))]
    exact congrArg (fun M => Matrix.map M (inclR (F := D.host.F) (AF D.host.F))) hγ0'
  refine ⟨⟨⟨_, hHR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ0, hγ0', rfl⟩)⟩, Subtype.ext (Units.ext ?_)⟩
  ext a b
  refine (finHom_entry V ⟨_, hHR⟩ γ0 rfl a b).trans ?_
  exact (hfin a b).symm

theorem ratMatch_bwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ' : Formalism.L2.Theta.GQ V) :
    ∃ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γE, hγE, eE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ'.2)
  have hR : Bridge.IsRatMat V γ' γE := eE.symm
  set κ := (frameEquiv P).symm (Bridge.ratF V γ') with hκ
  have he : Bridge.ratF V γ' = frameEquiv P κ := ((frameEquiv P).apply_symm_apply _).symm
  have hent := key κ γ' γE he hR
  have hmat : ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom := by
    ext a c; exact hent a c
  have hU := κ.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk, Set.mem_ofPred_eq] at hU
  have hc : ∀ x : D.host.E, (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)
      ((IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x) =
      ReciprocityTheory.Aut.conjAL D.host.E (Algebra.TensorProduct.includeLeftRingHom x) := fun x => by
    simp [ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.map_tmul]
  have hcT : ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom) =
      (ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) (γE : Matrix _ _ _)).map
        Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply, hc]
  have h0 : γE ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
    show (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) γE = 1
    apply Matrix.map_injective hinjL
    simp only
    rw [Matrix.map_mul, ← hcT, ← hmat, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hU
  refine ⟨⟨κ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γE, h0, Units.ext ?_⟩)⟩, he⟩
  rw [hmat]
  ext a c
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

end GlobalTheory.MtReadRat

namespace GlobalTheory.MtRead
open GlobalTheory.MtReadRat Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ratMatch_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  intro D V n hF P ⟨hn, hId⟩
  subst hn
  refine ⟨⟨ratMatch_fwd hF P hId, ratMatch_bwd hF P hId⟩, fun hn γ γ' γE e hR a c => ?_⟩
  simpa only [Fin.cast_eq_self] using entry_of_ratF hF P hId γ.1 γ' γE e hR a c

end GlobalTheory.MtRead

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

theorem _root_.GlobalTheory.T.exists_separating_character_conjugate_half_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  first | exact @GlobalTheory.DownLift.GenSplit.exists_sep_char | exact GlobalTheory.DownLift.GenSplit.exists_sep_char | (intros; apply GlobalTheory.DownLift.GenSplit.exists_sep_char <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

theorem _root_.GlobalTheory.T.thetaFunction_level_and_schrodinger_bounded_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  first | exact @GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support | exact GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support | (intros; apply GlobalTheory.DownLift.GenSplit.SupportBound.level_and_support <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

theorem _root_.GlobalTheory.T.schrodingerFunction_invariant_typePrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → ∀ (ϖ : OI v), Irreducible ϖ → ∀ h : GL (Fin D.R.r ⊕ Fin D.R.t) (OI v), (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (OI v)) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((h : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) f) := by
  first | exact @GlobalTheory.DownLift.GenSplit.schrodinger_type_inv | exact GlobalTheory.DownLift.GenSplit.schrodinger_type_inv | (intros; apply GlobalTheory.DownLift.GenSplit.schrodinger_type_inv <;> assumption)
end
