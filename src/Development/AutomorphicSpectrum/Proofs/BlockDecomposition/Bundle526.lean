module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle398
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle501
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.unitary_euclidean_model : ∀ {n : ℕ} (E : KMod n), ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) (ρ' : Matrix.unitaryGroup (Fin n) ℂ →* (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))), Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.dualRep_exists | exact GlobalTheory.CompanionTheory.RealCount.dualRep_exists | (intros; apply GlobalTheory.CompanionTheory.RealCount.dualRep_exists <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_inverse_reduction : PositivityTheory.SphericalProduct.InvStepU := by
  first | exact @GlobalTheory.CompanionTheory.InvStep.invStepU | exact GlobalTheory.CompanionTheory.InvStep.invStepU | (intros; apply GlobalTheory.CompanionTheory.InvStep.invStepU <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := GlobalTheory.T.iwahori_unipotent_datum L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (GlobalTheory.T.dominant_unipotent_contraction L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := GlobalTheory.T.hecke_character_exists_unique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := GlobalTheory.T.satake_power_nonvanishing L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end

section

noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.HarmCone

variable {n : ℕ}

def sg (lev : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (if lev a < lev b then 1 else 0) - (if lev b < lev a then 1 else 0)

theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) : 2 * rhoU lev a = ∑ b, sg lev a b := by
  simp only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]
  ring

theorem sg_anti (lev : Fin n → ℕ) (a b : Fin n) : sg lev a b = - sg lev b a := by
  unfold sg
  ring

theorem sg_cases (lev : Fin n → ℕ) (a b : Fin n) :
    sg lev a b = 1 ∨ sg lev a b = 0 ∨ sg lev a b = -1 := by
  unfold sg
  split_ifs <;> norm_num

theorem mul_sg_self (lev : Fin n → ℕ) (a b : Fin n) :
    ((lev a : ℝ) - lev b) * sg lev a b = -|(lev a : ℝ) - lev b| := by
  rcases lt_trichotomy (lev a) (lev b) with h | h | h
  · have h' : (lev a : ℝ) < lev b := by exact_mod_cast h
    have hs : sg lev a b = 1 := by
      unfold sg
      rw [if_pos h, if_neg (by omega)]
      norm_num
    rw [hs, abs_of_neg (by linarith)]
    ring
  · have hs : sg lev a b = 0 := by
      unfold sg
      rw [if_neg (by omega), if_neg (by omega)]
      norm_num
    rw [hs, h]
    simp
  · have h' : (lev b : ℝ) < lev a := by exact_mod_cast h
    have hs : sg lev a b = -1 := by
      unfold sg
      rw [if_neg (by omega), if_pos h]
      norm_num
    rw [hs, abs_of_pos (by linarith)]
    ring

theorem neg_abs_le_mul_sg (lev : Fin n → ℕ) (x : ℝ) (a b : Fin n) : -|x| ≤ x * sg lev a b := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith

theorem pair_root (f : Fin n → ℝ) (a b : Fin n) :
    ∑ x, f x * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) = f a - f b := by
  simp [mul_sub, Finset.sum_sub_distrib]

def dsg (lev lev' : Fin n → ℕ) (x b : Fin n) : ℝ := sg lev' x b - sg lev x b

theorem dsg_anti (lev lev' : Fin n → ℕ) (x b : Fin n) : dsg lev lev' x b = - dsg lev lev' b x := by
  unfold dsg
  rw [sg_anti lev' x b, sg_anti lev x b]
  ring

theorem dsg_nonneg (lev lev' : Fin n → ℕ) (x b : Fin n) :
    0 ≤ ((lev x : ℝ) - lev b) * dsg lev lev' x b := by
  unfold dsg
  rw [mul_sub, mul_sg_self]
  have := neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b
  linarith

theorem pairing_nonneg (lev lev' : Fin n → ℕ) :
    0 ≤ ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
  have e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [Finset.mul_sum]
  have e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    rw [Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dsg_anti lev lev' b x]
    ring
  have e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b
      = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b
  linarith

theorem harm_cone : N1 := by
  intro n lam _ lev lev' _ _ hc
  obtain ⟨c, hc0, hQ⟩ := hc
  have hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b := by
    intro x
    simp only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]
    ring
  have hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b
      = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) := by
    have e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) *
        ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) := by
      intro x
      rw [← hQx, hQ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]
  have hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
      have h2 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b)
      (hD ▸ pairing_nonneg lev lev')
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum
  have hz : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1
      (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
    have h3 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
    have h4 : (c a b : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h4 h
    · linarith
  funext x
  have h5 := hQ x
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5
  exact sub_eq_zero.1 h5

end GlobalTheory.CompanionTheory.HarmCone
end
end

section

open PositivityTheory.Rg.BcB.F.Eig

namespace GlobalTheory.CompanionTheory.BlockScalars

theorem diagOp_apply {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ)
    (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    (diagOp blk c x) j = c (blk j) * x j := by
  simp [diagOp, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem diagAlg : DiagAlg := by
  intro ι d blk c c' z
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x j
    simp [diagOp_apply, ContinuousLinearMap.mul_def, mul_assoc]
  · ext x j
    simp [diagOp_apply, add_mul]
  · ext x j
    simp [diagOp_apply]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [PiLp.inner_apply, diagOp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [RCLike.inner_apply]
    ring

end GlobalTheory.CompanionTheory.BlockScalars
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SpecModel

theorem twTr_unit (hL : LocAlg) {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}
    (σ : SmIrr (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) (KL n w))
    (h1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1) {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) :
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := hL E n w σ _ hlev f f hf hf
  obtain ⟨h8, -, -, -, -, -, -, h9⟩ := hL E n w σ _ hlev _ _ h7 h7
  have e : ((KL n w : Set (UL n w)).indicator fun _ => (((KL n w).relIndex (KL n w) : ℕ) : ℂ)) =
      (KL n w : Set (UL n w)).indicator 1 := by
    rw [Subgroup.relIndex_self]
    congr 1
    funext x
    simp
  rw [e] at h8 h9
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.finite_of_finrank_pos (by omega)
  rw [h8, h9, LinearMap.trace_one, h1]
  simp

theorem finprod_split {P : Type} (S : Set P) (B : Finset P) (hB : (↑B : Set P) ⊆ S) (F G : P → ℂ)
    (T : {w // w ∈ B} → ℂ) (hT : ∀ w, T w = F w.1) (hG : ∀ w ∈ S, w ∉ B → F w = G w)
    (hfin : ((S \ ↑B) ∩ Function.mulSupport F).Finite) :
    ∏ᶠ w ∈ S, F w = (∏ᶠ w ∈ S \ ↑B, G w) * ∏ w, T w := by
  have hon : ((↑B : Set P) ∩ Function.mulSupport F).Finite := B.finite_toSet.inter_of_left _
  have hB' : ∏ᶠ w ∈ (↑B : Set P), F w = ∏ w, T w := by
    rw [finprod_mem_coe_finset, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun w _ => (hT w).symm
  have hC : ∏ᶠ w ∈ S \ ↑B, F w = ∏ᶠ w ∈ S \ ↑B, G w :=
    finprod_mem_congr rfl fun w hw => hG w hw.1 hw.2
  have hS : ↑B ∪ (S \ ↑B) = S := Set.union_sdiff_cancel hB
  rw [← hS, finprod_mem_union' Set.disjoint_sdiff_right hon hfin, hS, hB', hC, mul_comm]

theorem specTrace : UModel → LocAlg → SpecTrace := by
  intro hU hL E _ _ _ n S B hB K' hK' hKB ι _ σ hfd hone g
  have : ∀ (i : ι) (w : {w // w ∈ B}), FiniteDimensional ℂ (fixed (σ i w.1).ρ (K' w.1)) :=
    fun i w => hfd i w.1 (hB w.2)
  obtain ⟨d, blk, u, h1, h2, h3⟩ := hU ι {w // w ∈ B} (fun i w => ↥(fixed (σ i w.1).ρ (K' w.1)))
    (fun i w => locOp (σ i w.1) (K' w.1) (g w.1))
  refine ⟨d, blk, u, h1, ?_, ?_⟩
  · intro k f hf hloc
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hoff : ((S \ ↑B) ∩ Function.mulSupport
        fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id).Finite := by
      have hev := hK'.2.and hf.2
      rw [Filter.eventually_cofinite] at hev
      refine hev.subset ?_
      rintro w ⟨⟨hwS, hwB⟩, hne⟩ ⟨e1, e2⟩
      apply hne
      have hlev := hK'.1 w
      have hH := hf.1 w
      rw [e1] at hlev hH
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = 1
      rw [e1, e2]
      exact twTr_unit hL (σ i w) hlev (hone i w hwS hwB) hH
    refine finprod_split S B hB (fun w => twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id)
      (fun w => twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id)
      (fun w => LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k)) ?_ ?_ hoff
    · intro w
      show LinearMap.trace ℂ _ (locOp (σ i w.1) (K' w.1) (g w.1) ^ k) =
        twTr (σ i w.1).ρ (KL n w.1) (K' w.1) (f w.1) LinearMap.id
      rw [← hloc i w.1 w.2]
      exact (hL E n w.1 (σ i w.1) (K' w.1) (hK'.1 w.1) (f w.1) (f w.1) (hf.1 w.1) (hf.1 w.1)).1.symm
    · intro w hwS hwB
      show twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
        twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id
      rw [hKB w hwS hwB]
  · intro i₀ hi
    exact h3 i₀ fun w => hi w.1 w.2

end GlobalTheory.CompanionTheory.SpecModel

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.TorusExpU

theorem torusExp : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp
  intro k _ _ _ _ n V _ _ π ϖ hϖ ξ c y hy hfix hx t
  have hord : ord k ϖ = 1 := by
    exact GlobalTheory.SmGL.ord_eq_one hϖ
  refine GlobalTheory.CompanionTheory.ExtCharU.extChar k n _ (jacB π) y ϖ ξ c hy hord ?_ ?_ t
  · intro s hs
    have h1 : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) s = 1 := by
      simpa using GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k hs
    have h2 : jacBU π s y = y := by simpa using hfix ⟨s, hs⟩
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, h1, h2]
    simp
  · intro x hxa
    have hD : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom)
        (fun i => ϖ ^ x i) = deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) := rfl
    have hne : ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, hD, hx x hxa, smul_smul]
    congr 1
    rw [Units.val_inv_eq_inv_val, mul_comm, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rfl

end GlobalTheory.CompanionTheory.TorusExpU

end
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.CharInf

theorem chWMap : ChWMap := by
  intro E _ _ n lam P
  rfl

end GlobalTheory.CompanionTheory.CharInf
end

section


theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
end
