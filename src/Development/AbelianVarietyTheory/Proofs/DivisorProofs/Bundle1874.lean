module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory

theorem eq_one_of_forall_norm_pow_sub_one_lt (w : ℂ) (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2) : w = 1 := by
  by_contra hw
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
  have hre : ∀ k : ℕ, 1 / 2 < (w ^ k).re := by
    intro k
    have h1 := (Complex.abs_re_le_norm (w ^ k - 1)).trans_lt (h k)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_lt.1 h1).1]
  have hsum : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, w ^ k).re := by
    rw [Complex.re_sum]
    have := Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hre k).le)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hnorm : (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, w ^ k‖ :=
    hsum.trans (Complex.re_le_norm _)
  have hgeom : ‖∑ k ∈ Finset.range N, w ^ k‖ * ‖w - 1‖ < 1 / 2 := by
    rw [← norm_mul, geom_sum_mul]; exact h N
  have : (N : ℝ) / 2 * ‖w - 1‖ < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm hd.le) hgeom
  have h2 : (N : ℝ) * ‖w - 1‖ < 1 := by linarith
  rw [div_lt_iff₀ hd] at hN
  linarith


open Filter Topology in
theorem psiLoc_eventually_trivial_integers {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) :
    ∀ᶠ v in Filter.cofinite, ∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1 := by
  classical
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F)
      (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
        (fun v => ⟨(y v).1, (y v).2⟩))
  have hι : Continuous ι := by
    have hs : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) =>
        RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
          (fun v => ⟨(y v).1, (y v).2⟩)) :=
      RestrictedProduct.isEmbedding_structureMap.continuous
    exact continuous_const.prodMk hs
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      refine Prod.ext rfl ?_
      show RestrictedProduct.structureMap _ _ _ _ = (0 : Af F)
      refine _root_.GlobalTheory.AdelicU.af_ext fun w => ?_
      rfl
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  have key : ∀ v, v ∉ I → ∀ x ∈ v.adicCompletionIntegers F, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x - 1‖ < 1 / 2 := by
    intro v hv x hx
    let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨x, hx⟩
    have hy : y ∈ (I : Set _).pi u := by
      intro a ha
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      have : y a = 0 := Pi.single_eq_of_ne hav _
      rw [this]; exact (hu a ha).2
    have hmem := hsub hy
    have hιy : ι y = LinearMap.inr F (Ainf F) (Af F) (singleFin v x) := by
      refine congrArg (LinearMap.inr F (Ainf F) (Af F)) (_root_.GlobalTheory.AdelicU.af_ext fun w => ?_)
      by_cases e : w = v
      · subst e; rw [evalV_singleFin_self]
        show ((y w : w.adicCompletion F)) = x
        simp [y]
      · rw [evalV_singleFin_ne e]
        show ((y w : w.adicCompletion F)) = 0
        simp [y, Pi.single_eq_of_ne e]
    simpa [hιy, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc] using hmem
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ x ∈ v.adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1}.Finite := by
    refine (I.finite_toSet).subset fun v hv => ?_
    by_contra hvI
    apply hv
    intro x hx
    refine eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_
    have hnx : n • x ∈ v.adicCompletionIntegers F := nsmul_mem hx n
    have := key v hvI (n • x) hnx
    have hpow : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (n • x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x ^ n := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc, map_nsmul]
      exact AddChar.map_nsmul_eq_pow ψ n _
    rwa [hpow] at this
  exact Filter.eventually_cofinite.2 hfin

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatVac

variable {F : Type} [Field F] [NumberField F]

def liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Fv F v →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v)

def psiAt (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (liftV v).toAddMonoidHom

theorem psiAt_apply (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : Fv F v) :
    psiAt ψ v x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x := rfl

def locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : W →+ (κ → Fv F v) × (κ → Fv F v) where
  toFun w := (fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).1 k), fun k => GlobalTheory.AdelicU.evFin F v ((co.e w).2 k))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem evFin_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) : GlobalTheory.AdelicU.evFin F v (liftV v a) = a :=
  GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem at_liftV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (liftV v a) := by
  intro u hu
  refine Prod.ext (by change u.1 * 0 = 0; exact mul_zero _) ?_
  change u.2 * GlobalTheory.AdelicU.singleFin v a = 0
  apply GlobalTheory.AdelicU.af_ext
  intro w
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · subst hw
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, mul_zero]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem symp_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (a a' : AF F)
    (x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB (a • x) (a' • y) =
      a * a' * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  have h : ξ * ∑ i, ∑ j, ∑ k, ∑ l, (a • x) i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((a' • y) k l)
      = (a * a') • (ξ * ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (y k l)) := by
    simp only [Matrix.smul_apply, map_smul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h, map_smul, smul_eq_mul]

end GlobalTheory.LatVac

namespace GlobalTheory.LatVac

theorem latAtV_at_stable : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) ∧
    ∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      GlobalTheory.LatVac.liftV v a • γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y v
  constructor
  · intro γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
      intro u hu
      rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
    | zero => intro u _; exact smul_zero u
    | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
    | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]
  · intro a ha γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      rw [smul_smul]
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a • a', ?_, ?_, x, hx, y, hy, rfl⟩
      · intro u hu
        rw [smul_eq_mul, smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [smul_eq_mul, map_mul, evFin_liftV]
        exact mul_mem ha hv
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LatVac
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.CompactCharDual

theorem eq_one_of_pow_close {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitNormRealPartBound.main
  | exact _root_.GlobalTheory.UnitNormRealPartBound.main
  | (apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitNormRealPartBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitNormRealPartBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitNormRealPartBound.main ..)

theorem exists_ball_ker {K : Type} [NormedAddCommGroup K] [IsUltrametricDist K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) : ∃ δ > 0, ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun x hx => eq_one_of_pow_close fun n => ?_⟩
  have := h (x := n • x) (by
    rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
  rwa [AddChar.map_zero_eq_one, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this

theorem mem_of_separates {Q : Type} [AddCommGroup Q] [Finite Q] (H : AddSubgroup (AddChar Q ℂ))
    (h : ∀ x : Q, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 1) (χ : AddChar Q ℂ) : χ ∈ H := by
  by_contra hχ
  have h0 : (QuotientAddGroup.mk χ : AddChar Q ℂ ⧸ H) ≠ 0 := fun e => hχ ((QuotientAddGroup.eq_zero_iff _).1 e)
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_apply_ne_zero.2 h0
  obtain ⟨x, hx⟩ := (AddChar.doubleDualEquiv (α := Q)).surjective (Λ.compAddMonoidHom (QuotientAddGroup.mk' H))
  have hev : ∀ φ : AddChar Q ℂ, φ x = Λ (QuotientAddGroup.mk φ) := fun φ => DFunLike.congr_fun hx φ
  by_cases hx0 : x = 0
  · exact hΛ (by rw [← hev, hx0, AddChar.map_zero_eq_one])
  · obtain ⟨φ, hφ, hφx⟩ := h x hx0
    exact hφx (by rw [hev, (QuotientAddGroup.eq_zero_iff _).2 hφ, AddChar.map_zero_eq_one])

theorem exists_lift {G : Type} [AddCommGroup G] (N : AddSubgroup G) (φ : AddChar G ℂ)
    (hφ : ∀ x ∈ N, φ x = 1) : ∃ Λ : AddChar (G ⧸ N) ℂ, ∀ x : G, Λ x = φ x := by
  refine ⟨⟨Quotient.lift φ fun a b hab => ?_, φ.map_zero_eq_one, ?_⟩, fun x => rfl⟩
  · have := hφ _ (QuotientAddGroup.leftRel_apply.1 hab)
    rw [← add_neg_cancel_left a b, AddChar.map_add_eq_mul, this, mul_one]
  · rintro ⟨a⟩ ⟨b⟩
    exact φ.map_add_eq_mul a b

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ]
    (ψ₀ : AddChar K ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (L : AddSubgroup (κ → K)) (hL : IsCompact (L : Set (κ → K)))
    (L' : AddSubgroup (κ → K)) (hL' : IsOpen (L' : Set (κ → K)))
    (χ : (κ → K) → ℂ) (hmul : ∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') (htriv : ∀ y ∈ L, y ∈ L' → χ y = 1) :
    ∃ x₀ : κ → K, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  classical
  obtain ⟨δ, hδ, hψδ⟩ := exists_ball_ker ψ₀ hc
  obtain ⟨r, hr, hrL'⟩ := Metric.isOpen_iff.1 hL' 0 L'.zero_mem
  obtain ⟨t₁, ht₁⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (DFunLike.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  have ht0 : 0 < ‖t₁‖ := norm_pos_iff.2 fun h => ht₁ (by rw [h, AddChar.map_zero_eq_one])
  set ρ := ‖t₁‖ / r with hρ
  have hρ0 : 0 < ρ := div_pos ht0 hr
  set η := min r (δ / ρ) with hη
  have hη0 : 0 < η := lt_min hr (div_pos hδ hρ0)

  have small : ∀ a y : κ → K, ‖a‖ ≤ ρ → ‖y‖ < η → ψ₀ (a ⬝ᵥ y) = 1 := by
    intro a y ha hy
    have key : ∀ s : Finset κ, (∀ i ∈ s, ψ₀ (a i * y i) = 1) → ψ₀ (∑ i ∈ s, a i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert i s hi ih =>
        intro hf
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, hf i (Finset.mem_insert_self _ _),
          ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), one_mul]
    show ψ₀ (∑ i, a i * y i) = 1
    refine key Finset.univ fun i _ => hψδ _ ?_
    rw [norm_mul]
    have h1 : ‖a i‖ ≤ ρ := (norm_le_pi_norm a i).trans ha
    have h2 : ‖y i‖ < δ / ρ := ((norm_le_pi_norm y i).trans_lt hy).trans_le (min_le_right _ _)
    calc ‖a i‖ * ‖y i‖ ≤ ρ * ‖y i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ < ρ * (δ / ρ) := mul_lt_mul_of_pos_left h2 hρ0
      _ = δ := mul_div_cancel₀ _ hρ0.ne'
  let M : AddSubgroup (κ → K) :=
    { carrier := {y | ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1}
      add_mem' := fun {y y'} hy hy' a ha => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, hy a ha, hy' a ha, mul_one]
      zero_mem' := fun a _ => by rw [dotProduct_zero, AddChar.map_zero_eq_one]
      neg_mem' := fun {y} hy a ha => by
        rw [dotProduct_neg, ← neg_dotProduct]
        exact hy (-a) (by rwa [norm_neg]) }
  have hMmem : ∀ y, y ∈ M ↔ ∀ a : κ → K, ‖a‖ ≤ ρ → ψ₀ (a ⬝ᵥ y) = 1 := fun y => Iff.rfl

  have hML' : ∀ y ∈ M, y ∈ L' := by
    intro y hy
    refine hrL' (mem_ball_zero_iff.2 ?_)
    rw [pi_norm_lt_iff hr]
    intro k
    by_contra hk
    push_neg at hk
    have hyk : 0 < ‖y k‖ := hr.trans_le hk
    refine ht₁ ?_
    have hnorm : ‖(Pi.single k (t₁ / y k) : κ → K)‖ ≤ ρ := by
      refine (pi_norm_le_iff_of_nonneg hρ0.le).2 fun i => ?_
      by_cases hi : i = k
      · subst hi
        rw [Pi.single_eq_same, norm_div]
        exact div_le_div_of_nonneg_left ht0.le hr hk
      · rw [Pi.single_eq_of_ne hi, norm_zero]; exact hρ0.le
    have := (hMmem y).1 hy _ hnorm
    rwa [single_dotProduct, div_mul_cancel₀ _ (norm_pos_iff.1 hyk)] at this

  let U : AddSubgroup (κ → K) :=
    { carrier := Metric.ball 0 η
      add_mem' := fun {a b} ha hb => mem_ball_zero_iff.2
        ((IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)))
      zero_mem' := Metric.mem_ball_self hη0
      neg_mem' := fun {a} ha => by simpa using ha }
  have hUM : U ≤ M := fun y hy a ha => small a y ha (mem_ball_zero_iff.1 hy)
  let N : AddSubgroup L := M.addSubgroupOf L
  have hNo : IsOpen (N : Set L) := by
    refine AddSubgroup.isOpen_mono (H₁ := U.addSubgroupOf L)
      (fun y hy => AddSubgroup.mem_addSubgroupOf.2 (hUM (AddSubgroup.mem_addSubgroupOf.1 hy))) ?_
    exact (Metric.isOpen_ball (x := (0 : κ → K)) (ε := η)).preimage continuous_subtype_val
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  haveI : Finite (L ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNo

  let e : (κ → K) → AddChar L ℂ := fun a =>
    { toFun := fun y => ψ₀ (a ⬝ᵥ (y : κ → K))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun y y' => by
        rw [AddSubgroup.coe_add, dotProduct_add, AddChar.map_add_eq_mul] }
  have he : ∀ a (y : L), e a y = ψ₀ (a ⬝ᵥ (y : κ → K)) := fun _ _ => rfl
  have hχ0 : χ 0 = 1 := htriv 0 L.zero_mem L'.zero_mem
  let χL : AddChar L ℂ :=
    { toFun := fun y => χ y
      map_zero_eq_one' := hχ0
      map_add_eq_mul' := fun y y' => hmul _ y.2 _ y'.2 }
  obtain ⟨X, hX⟩ := exists_lift N χL fun y hy => htriv _ y.2 (hML' _ hy)
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {Λ | ∃ a : κ → K, ‖a‖ ≤ ρ ∧ ∀ y : L, Λ y = ψ₀ (a ⬝ᵥ (y : κ → K))}
      add_mem' := by
        rintro Λ Λ' ⟨a, ha, h⟩ ⟨b, hb, h'⟩
        refine ⟨a + b, (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb), fun y => ?_⟩
        rw [AddChar.add_apply, h, h', add_dotProduct, AddChar.map_add_eq_mul]
      zero_mem' := ⟨0, by rw [norm_zero]; exact hρ0.le, fun y => by simp⟩
      neg_mem' := by
        rintro Λ ⟨a, ha, h⟩
        refine ⟨-a, by rwa [norm_neg], fun y => ?_⟩
        rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, AddSubgroup.coe_neg, dotProduct_neg, neg_dotProduct] }
  have hsep : ∀ q : L ⧸ N, q ≠ 0 → ∃ Λ ∈ H, Λ q ≠ 1 := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hyN : (y : κ → K) ∉ M := fun h => hq ((QuotientAddGroup.eq_zero_iff _).2 h)
    rw [hMmem] at hyN
    push_neg at hyN
    obtain ⟨a, ha, hay⟩ := hyN
    obtain ⟨Λ, hΛ⟩ := exists_lift N (e a) fun z hz => hz a ha
    exact ⟨Λ, ⟨a, ha, fun z => hΛ z⟩, by rw [hΛ]; exact hay⟩
  obtain ⟨a, -, ha⟩ := mem_of_separates H hsep X
  exact ⟨a, fun y hy => (hX ⟨y, hy⟩).symm.trans (ha ⟨y, hy⟩)⟩

end GlobalTheory.CompactCharDual

namespace GlobalTheory.CompactCharDual

theorem exists_dotProduct_eq_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  intro F _ _ v κ _ ψ₀ hc hne L hL L' hL' χ hmul htriv
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  exact exists_dotProduct_eq ψ₀ hc hne L hL L' hL' χ hmul htriv

end GlobalTheory.CompactCharDual
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.smooth_vector_automorphic_derivatives : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ F, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → ∃ ψ, Repr V μ 𝓕 F ψ ∧ IsAutFun V ψ ∧ (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧ ∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) ∧ Repr V μ 𝓕 (l.foldr (dL2 θ V ρ) F) (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) := by
  first | exact @GlobalTheory.SmoothRep.exists_smooth_repr | exact GlobalTheory.SmoothRep.exists_smooth_repr | (intros; apply GlobalTheory.SmoothRep.exists_smooth_repr <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem holForm_zCusp_of_mem_mult : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, HolForm θ M w J χ (T v) ∧ ZCusp V (T v) := by
  intro hP D θ V S M w v hθ hM hw hv J χ T hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  have hd := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ (h.aut v) (h.cusp v)
  have hh := GlobalTheory.T.multiplicityMap_extremalVector_holomorphicType D θ V S M w v hθ hM hw hv J χ T h
  exact ⟨⟨(h.aut v).toIsAutFun, hd.bounded, h.lev v, hh⟩,
    GlobalTheory.T.transvectionCuspidal_of_rapidDecay_holomorphicType D θ V S M w hθ hM _ (h.aut v).toIsAutFun hh hd⟩

end GlobalTheory.HolDict
end
