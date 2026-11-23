module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCells
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.kernelsCommuteExplicitConstAlt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q (resChar ψ hψ q) (K φ).1 := by
  first | exact @GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst | exact GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst | (intros; apply GlobalTheory.KernelCommExplicit.kernelsCommuteExplicitConst <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  first | exact @GlobalTheory.PClassAlg.blockDiag_mem_KO | exact GlobalTheory.PClassAlg.blockDiag_mem_KO | (intros; apply GlobalTheory.PClassAlg.blockDiag_mem_KO <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

theorem _root_.GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero | exact GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero | (intros; apply GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem oneIndexAt_of_classAt_supportAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c H p hp1 hpc h hE
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c H p hp1 hpc h hE
  obtain ⟨γ, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  have hmul : ∀ (a b : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k) (Ψ : type_of% ((S.T t).Phi j c H)),
      om (S.μ (j + 1)) 1 (a * b) Ψ = om (S.μ (j + 1)) 1 a (om (S.μ (j + 1)) 1 b Ψ) :=
    fun a b Ψ => by rw [← om_mul, one_mul]
  have hne : opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0
    apply hE
    rw [mul_assoc, hmul, (opE_om_embX k _ _ c p hp1 hpc S.ψ ν _ _).1, hmul,
      opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν _ _ g hg, h0]
    funext y
    simp [om]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE S.ψ ν p (om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H)) x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  classical
  obtain ⟨e, he⟩ : ∃ e, om (S.μ (j + 1)) 1 u ((S.T t).Phi j c H) (affPt p x₀ e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx₀
    simp [opE, hc]
  have hΦ : (S.T t).Phi j c H ((u⁻¹).val * affPt p x₀ e) ≠ 0 := by
    intro h0
    apply he
    simp only [om, Units.val_one, Matrix.mul_one, h0, mul_zero]
  obtain ⟨r', hr', u', hu', rfl⟩ := hS j c H p hp1 hpc u hu x₀ e hΦ
  exact ⟨embX c γ * g * r', mul_mem hr hr', u', hu', by group⟩

end GlobalTheory.SymChain
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

theorem val_row_le_of_Phi_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + 1 + c = s) (r : ℕ)
    (hc : c = 2 * r) (w : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hw : (S.T t).Phi j (c + 1) (by omega) w ≠ 0) (y : XIx (Fin κ) t j) :
    valuation k (w (Sum.inr ⟨r, by omega⟩) (Sum.inl y)) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : (S.T t).Phi j (c + 1) (by omega) w = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') w).submatrix (ixSucc _ t j) id) := rfl
  rw [hΦ] at hw
  have hI := TypeDatum.intM_of_Phi_ne_zero _ _ hw ((ixSucc _ t j).symm (o.symm (Sum.inr ⟨r, by omega⟩)))
    (o'.symm (Sum.inl y))
  have hw' : w = fromBlocks w.toBlocks₁₁ w.toBlocks₁₂ w.toBlocks₂₁ w.toBlocks₂₂ := (fromBlocks_toBlocks w).symm
  rw [hw'] at hI
  simp [LatFrame.coords, typeFrame, embA, GlobalTheory.SplitFlip.diagGL, fromBlocks_multiply] at hI
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀] at hI
  have hv : 0 < valuation k ((S.ϖ : k) ^ (r + 1)) := by
    rw [zero_lt_iff]; simp
  rw [Units.val_pow_eq_pow_val]
  change valuation k (w.toBlocks₂₁ ⟨r, by omega⟩ y) ≤ _
  rwa [inv_mul_le_iff₀ hv, mul_one] at hI

theorem flRow_eq_zero_of_not_mem_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by
  intro k _ _ _ _ _ _ ν s κ S t _ _ j c H r hc x hx
  obtain ⟨y, hy⟩ : ∃ y, ¬ valuation k (x (Sum.inr ()) y) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
    by_contra h
    push_neg at h
    exact hx fun i => h i
  unfold flRow opE
  refine (integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)).trans (integral_zero _ _)
  simp only [Pi.zero_apply]
  refine mul_eq_zero_of_left ?_ _
  by_contra hne
  have h1 := val_row_le_of_Phi_ne_zero S t j c H r hc _ hne y
  apply hy
  convert h1 using 2
  simp [affPt, basePt, rowAt, Free]
end GlobalTheory.LocFlat
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

theorem add_right_mem_SB {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem flRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p Φ₁ Φ₂ h₁ h₂
  funext x
  have H := opE_smul_add p hψ ν (1 : ℂ)
    (add_right_mem_SB h₁ (rowAt n c p (x (Sum.inr ()))))
    (add_right_mem_SB h₂ (rowAt n c p (x (Sum.inr ()))))
  have H' := congrFun H x.toRows₁
  simp only [one_smul, Pi.add_apply] at H'
  simp only [flRow, Pi.add_apply]
  rw [← H']
  rfl

end GlobalTheory.LocFlat
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat

theorem colE_neg_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [colE, upU, -Matrix.coe_units_inv, Units.inv_mk, neg_ite]

theorem affPt_add_colAt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (y : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e + colAt n' c (q.val + 1) y = mat x₀ (ext0 (Free (q.val + 1)) e + gCol q y) := by
  classical
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [affPt_eq, mat, ext0, colAt, gCol, Free]
  · by_cases h : s = q.castSucc
    · subst h; simp [affPt_eq, mat, ext0, colAt, gCol, Free]
    · have h' : ¬ s.val = q.val := fun hh => h (Fin.ext (by simpa using hh))
      simp [affPt_eq, mat, ext0, colAt, gCol, h, h']
  · simp [affPt_eq, mat, ext0, colAt, gCol]
  · simp [affPt_eq, mat, ext0, colAt, gCol]

theorem ch_add_colAt {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end GlobalTheory.LocFlat.ColTranslate

namespace GlobalTheory.LocFlat
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat.ColTranslate

theorem flCol_eq_opE_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc Φ hΦ x
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp; omega⟩
  have hcont : Continuous Φ := hΦ.1.continuous
  have h1 := opE_colE hψ ν 1 q q (χ := fun _ => (1 : ℂ)) continuous_const hcont x.toCols₁
    (-fun r => x r (Sum.inr ()))
  simp only [om_colE, colE_neg_inv, one_mul, neg_neg] at h1
  refine Eq.trans ?_ h1.symm
  rw [flCol]
  unfold opE
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  simp only
  rw [← affPt_add_colAt, big, ch_add_colAt, one_mul]

end GlobalTheory.LocFlat
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat


open GlobalTheory.RootEx.Exchange in
theorem flRow_eq_opE_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp hpc Φ hΦ x
  have := hν
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, p = q.val + 1 := ⟨⟨p - 1, by omega⟩, by simp only; omega⟩
  have h := opE_rowE hψ ν 1 q (χ := fun _ => (1 : ℂ)) continuous_const hΦ.1.continuous x.toRows₁
    (x (Sum.inr ()))
  refine Eq.trans ?_ (h.symm.trans ?_)
  swap
  · rw [one_mul]
    congr 1
    funext z
    exact om_rowE _ _ _ _ _
  unfold flRow opE
  congr 1
  funext e
  have key : affPt (q.val + 1) x.toRows₁ e + rowAt n c (q.val + 1) (x (Sum.inr ())) =
      mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ()))) := by
    rw [affPt_eq]
    ext r s
    rcases r with r | r <;> rcases s with s | s <;>
      simp [mat, rowAt, gRow, Fin.val_inj, add_assoc]
  have hch : ch (mat x.toRows₁ (ext0 (Free (q.val + 1)) e + gRow q (x (Sum.inr ())))) =
      ch (affPt (q.val + 1) x.toRows₁ e) := by
    rw [affPt_eq]
    unfold ch
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mat, gRow]
  simp only [big]
  rw [key, hch, one_mul]

end GlobalTheory.LocFlat
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem _root_.GlobalTheory.T.isQuotInt_cells_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  first | exact @GlobalTheory.CellQuotInt.isQuotInt_cells | exact GlobalTheory.CellQuotInt.isQuotInt_cells | (intros; apply GlobalTheory.CellQuotInt.isQuotInt_cells <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  first | exact @GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne | exact GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne | (intros; apply GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega

def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)

theorem fill_eq (ρ : ℕ) (lρ : Fin c) (hl : lρ.val = ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ ∪ upSet ρ) x y =
      affPt (ρ + 1) (fun r s => x (Sum.inl r) (Sum.inl s)) (fun rs => y ((freeEquiv n n' c ρ).symm rs)) +
        rowAt n c (ρ + 1) (fun s => x (Sum.inr lρ) (Sum.inl s)) := by
  ext r q
  simp only [fillAt, affPt, Matrix.add_apply, Matrix.of_apply]
  by_cases hI : (r, q) ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
  · have hF : Free (ρ + 1) (r, q) := (mem_transSet_union_upSet ρ _).1 hI
    rw [dite_eq_left hI, dite_eq_left hF]
    have h1 : (freeEquiv n n' c ρ).symm ⟨(r, q), hF⟩ = ⟨(r, q), hI⟩ := rfl
    rw [h1]
    rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
  · have hF : ¬ Free (ρ + 1) (r, q) := fun hF => hI ((mem_transSet_union_upSet ρ _).2 hF)
    rw [dite_eq_right hI, dite_eq_right hF]
    by_cases hE : (r, q) ∈ (fixSet ρ ∪ lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
    · rw [if_pos hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
    · rw [if_neg hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state

theorem ch_add_rowAt (p : ℕ) (A : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (u : n' → k) :
    ch (A + rowAt n c p u) = ch A := by
  simp [ch, rowAt, Matrix.fromBlocks]

theorem piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by
  funext rs
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

end GlobalTheory.RedFlatRow


open GlobalTheory.RedFlatRow in
theorem GlobalTheory.RedFlatRow.red_eq_flRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  intro k _ _ _ _ _ _ ψ ν hν n n' _ _ _ _ c ρ _ lρ hl Φ x
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ => k)
    (fun _ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} => ν) (freeEquiv n n' c ρ)
  simp only [GlobalTheory.PartRed.red, GlobalTheory.LocFlat.flRow, opE]
  refine Eq.trans ?_ (hmp.integral_comp' _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piCongrLeft_freeEquiv, fill_eq ρ lρ hl x y, GlobalTheory.PartRed.chL_apply, ch_add_rowAt]
  rfl
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat

theorem integral_pi_subtype_iff {k α : Type} [MeasurableSpace k] {P Q : α → Prop} {i1 : Fintype (Subtype P)}
    {i2 : Fintype (Subtype Q)} (h : ∀ a, P a ↔ Q a) (ν : Measure k) (F : (Subtype P → k) → ℂ)
    (G : (Subtype Q → k) → ℂ) (hFG : ∀ a, F a = G (fun e => a ⟨e.1, (h e.1).2 e.2⟩)) :
    ∫ a, F a ∂(Measure.pi fun _ => ν) = ∫ e, G e ∂(Measure.pi fun _ => ν) := by
  obtain rfl : P = Q := funext fun a => propext (h a)
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  obtain rfl : F = G := funext hFG
  rfl

def readPart {k : Type} {n n' : Type} {c : ℕ} (ρ : ℕ) (h : ρ < c + 1)
    (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix n (n' ⊕ Unit) k :=
  Matrix.of fun r q => Sum.elim (fun s => t (.inl r) (.inl s)) (fun _ => t (.inl r) (.inr ⟨ρ, h⟩)) q

section
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_itFree (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : e ∈ itFree n n' c ρ ↔ Free (ρ + 1) e := by
  simp [itFree]

theorem mem_evAll (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ evAll n n' c ρ ↔ ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e := by
  simp [evAll]

variable {k : Type} [Field k]

theorem fill_eq (ρ : ℕ) (h : ρ < c + 1) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (a : {e // e ∈ itFree n n' c ρ} → k) :
    fill (evAll n n' c ρ) (itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) t a =
      affPt (ρ + 1) (readPart ρ h t).toCols₁ (fun e => a ⟨e.1, (mem_itFree ρ e.1).2 e.2⟩) +
        colAt n' c (ρ + 1) (fun r => readPart ρ h t r (Sum.inr ())) := by
  ext r q
  simp only [fill, affPt, Matrix.of_apply, Matrix.add_apply]
  by_cases hF : Free (ρ + 1) (r, q)
  · rw [dite_eq_left ((mem_itFree ρ _).2 hF), dite_eq_left hF]
    rcases r with r | l <;> rcases q with s | i
    · exact hF.elim
    · have h1 : ρ + 1 < i.val + 1 := hF
      have h2 : i.val ≠ ρ := by omega
      simp [basePt, colAt, h2]
    · simp [basePt, colAt]
    · have h1 : l.val < i.val := hF
      have h2 : l.val ≠ i.val := by omega
      simp [basePt, colAt, h2]
  · rw [dite_eq_right (fun hh => hF ((mem_itFree ρ _).1 hh)), dite_eq_right hF]
    by_cases hR : IsRead n n' c ρ (r, q)
    · rw [if_neg (fun hh => ((mem_evAll ρ _).1 hh).2 hR)]
      rcases r with r | l <;> rcases q with s | i
      · simp [basePt, colAt, readPart]
      · have h1 : i.val = ρ := hR
        obtain rfl : i = ⟨ρ, h⟩ := Fin.ext h1
        simp [basePt, colAt, readPart]
      · exact hR.elim
      · exact hR.elim
    · rw [if_pos ((mem_evAll ρ _).2 ⟨hF, hR⟩)]
      rcases r with r | l <;> rcases q with s | i
      · exact (hR trivial).elim
      · have h1 : i.val ≠ ρ := hR
        simp [basePt, colAt, h1]
      · simp [basePt, colAt]
      · simp [basePt, colAt]

theorem ch_add_colAt (p : ℕ) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : n → k) :
    ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]

end

theorem red_eq_zero_of_flCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  intro k _ _ _ _ _ _ ψ ν n n' _ _ _ _ c ρ hc Φ hΦ t
  have h : ρ < c + 1 := by omega
  rw [← hΦ (readPart ρ h t)]
  unfold red flCol opE
  refine integral_pi_subtype_iff (mem_itFree ρ) ν _ _ fun a => ?_
  beta_reduce
  rw [fill_eq ρ h t a, ch_add_colAt, mul_comm]

end GlobalTheory.FlatRed
end
