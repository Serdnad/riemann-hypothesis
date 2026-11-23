module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle520
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.LowestKType.DegBound

theorem deg_X_mul_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv_X_mul {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b (MvPolynomial.X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_mul_pderiv _ _ _) ?_)
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (MvPolynomial.totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (MvPolynomial.totalDegree_smul_le _ _).trans (h P)

theorem one_mem_nonRaising (σ : Type) : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ :=
  fun _ => le_rfl

end GlobalTheory.LowestKType.DegBound

namespace GlobalTheory.LowestKType

open GlobalTheory.LowestKType.DegBound

theorem kop_totalDegree_le (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m)
    (hab : Cpt w τ a b) (d : ℕ) (P : PolF D m n) (hP : P.totalDegree ≤ d) :
    (kop w τ a b P).totalDegree ≤ d := by
  classical
  refine le_trans ?_ hP
  suffices h : kop w τ a b ∈ nonRaising (FVar D m n) from h P
  unfold kop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hil : i = a ∧ l = b
  · obtain ⟨rfl, rfl⟩ := hil
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_)
    · intro Q
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, if_true, one_smul]
      unfold Cpt at hab
      by_cases hi : (i : ℕ) < w.p τ
      · have hl : (l : ℕ) < w.p τ := hab.1 hi
        simp only [hi, hl, decide_true, if_true, Module.End.mul_apply, LinearMap.mulLeft_apply]
        exact deg_X_mul_pderiv _ _ _
      · have hl : ¬ (l : ℕ) < w.p τ := fun h => hi (hab.2 h)
        simp only [hi, hl, decide_false, Bool.false_eq_true, if_false, Module.End.mul_apply,
          LinearMap.mulLeft_apply, LinearMap.neg_apply,
          MvPolynomial.totalDegree_neg]
        exact deg_pderiv_X_mul _ _ _
    · split_ifs
      · exact Submodule.smul_mem _ _ (one_mem_nonRaising _)
      · exact Submodule.zero_mem _
  · have : Matrix.single a b (1 : ℂ) i l = 0 := by
      rw [Matrix.single_apply]
      split_ifs with h
      · exact absurd ⟨h.1.symm, h.2.symm⟩ hil
      · rfl
    rw [this, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.LowestKType
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.UpInj

def DCRep {Γ : Type} [Group Γ] (c : Γ →* Γ) (K : Subgroup Γ) (α : Γ) (C : Finset Γ) : Prop :=
  (∀ δ ∈ C, c δ = δ ∧ ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ δ = k₁ * α * k₂) ∧
  ∀ x, (∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ x = k₁ * α * k₂) →
    ∃! δ, δ ∈ C ∧ δ⁻¹ * x ∈ K ∧ c (δ⁻¹ * x) = δ⁻¹ * x

variable {D : D7}

def cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GfC V →* GfC V where
  toFun g := ⟨GlobalTheory.LevelProduct.cmp V v g, GlobalTheory.LevelProduct.cmp_mem_GfC V v g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem cf_val (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    (cf V v g : GA D V) = GlobalTheory.LevelProduct.cmp V v g := rfl

theorem isFinIdem_fE (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (GlobalTheory.LevelProduct.fE D v) :=
  ⟨_, GlobalTheory.LevelProduct.epsF_spec v, rfl⟩

theorem cf_supp (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    SuppF V (GlobalTheory.LevelProduct.fE D v) (cf V v g : GA D V) := GlobalTheory.LevelProduct.cmp_supp V v g

theorem cmp_eq_self {V : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V}
    (h : SuppF V (GlobalTheory.LevelProduct.fE D v) g) : GlobalTheory.LevelProduct.cmp V v g = g := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, ← (GlobalTheory.IdemSupport.suppF_iff V _ g).1 h, GlobalTheory.IdemSupport.mix_self]

theorem cf_eq_self_iff (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) :
    cf V v g = g ↔ SuppF V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) :=
  ⟨fun h => h ▸ cf_supp V v g, fun h => Subtype.ext (cmp_eq_self h)⟩

theorem trivAt_of_cf_eq_one (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) (h : cf V v g = 1) :
    TrivAt V (GlobalTheory.LevelProduct.fE D v) (g : GA D V) := by
  have e : GlobalTheory.LevelProduct.cmp V v (g : GA D V) = 1 := congrArg Subtype.val h
  have := GlobalTheory.LevelProduct.cmp_triv V v (g : GA D V)
  rwa [e, inv_one, mul_one] at this

theorem cf_cf (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GfC V) : cf V v (cf V v g) = cf V v g :=
  (cf_eq_self_iff V v _).2 (cf_supp V v g)

theorem cf_orth (V : HSp D) {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) (g : GfC V) :
    cf V w (cf V v g) = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have ho : GlobalTheory.LevelProduct.fE D w * GlobalTheory.LevelProduct.fE D v = 0 :=
    GlobalTheory.IdemSupport.place_orth hΦ (GlobalTheory.LevelProduct.epsF_spec w) (GlobalTheory.LevelProduct.epsF_spec v) (Ne.symm hvw)
  set h := cf V v g with hh
  have hs := cf_supp V v g
  have ht : TrivAt V (GlobalTheory.LevelProduct.fE D w) (h : GA D V) := by
    intro a b
    rw [← hs a b, ← mul_assoc, ho, zero_mul]
  apply Subtype.ext
  show GlobalTheory.LevelProduct.cmp V w (h : GA D V) = 1
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.LevelProduct.mt_cmp, GlobalTheory.IdemSupport.mt_one]
  have e : GlobalTheory.LevelProduct.fE D w • mt V (h : GA D V) =
      GlobalTheory.LevelProduct.fE D w • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext a b
    have := ht a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at this
    exact this
  rw [e, GlobalTheory.IdemSupport.mix_self]

abbrev KR {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Subgroup (GfC (Wc D i)) :=
  (levW R i).subgroupOf (GfC (Wc D i))

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem kr_mem_iff (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    g ∈ KR R i ↔ ∀ v, cf (Wc D i) v g ∈ KR R i := by
  have hH : (R.datWp i R.triv).P.H = ⊥ := rfl
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact ⟨fun h v => GlobalTheory.LevelProduct.cmp_mem_of_mem hH h v, fun h => GlobalTheory.LevelProduct.mem_of_cmp_mem hH g.2 h⟩

theorem kr_finite (R : RealDat D A Ks) (i : Fin D.R.m) (g : GfC (Wc D i)) :
    {v | cf (Wc D i) v g ∉ KR R i}.Finite := by
  simp only [KR, Subgroup.mem_subgroupOf, cf_val]
  exact GlobalTheory.LevelProduct.finite_cmp (g : GA D (Wc D i))

end GlobalTheory.UpInj

end
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

noncomputable section

open Real Complex
open scoped FourierTransform

namespace GlobalTheory.FourierDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

def pairL (u : Fin n → Cinf E) : (Fin n → Cinf E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, ∑ w, 2 * (x i w * u i w).re
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul, RingHom.id_apply,
          smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring }

theorem pairL_apply (u x : Fin n → Cinf E) : pairL u x = ∑ i, ∑ w, 2 * (x i w * u i w).re := rfl

instance isAddHaarMeasure_volume : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance isAddHaarMeasure_infMeasure : (infMeasure E n).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

theorem hasFDerivAt_kernel (u x : Fin n → Cinf E) :
    HasFDerivAt (fun y => (𝐞 (-pairL u y) : ℂ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * π * I * 𝐞 (-pairL u x))).comp (-pairL u)) x :=
  by
    have h1 := (Real.hasDerivAt_fourierChar (-pairL u x)).hasFDerivAt
    have h2 : HasFDerivAt (fun y => -pairL u y) (-pairL u) x := (pairL u).hasFDerivAt.neg
    exact h1.comp x h2

theorem fderiv_kernel (u x v : Fin n → Cinf E) :
    fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v = -(2 * π * I * (pairL u v : ℂ)) * 𝐞 (-pairL u x) := by
  rw [(hasFDerivAt_kernel u x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.real_smul]
  push_cast
  ring

theorem continuous_kernel (u : Fin n → Cinf E) : Continuous (fun y => (𝐞 (-pairL u y) : ℂ)) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_kernel u x).continuousAt

theorem infFourier_fderiv {f : (Fin n → Cinf E) → ℂ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (v u : Fin n → Cinf E) :
    infFourier (fun y => fderiv ℝ f y v) u = (2 * π * I * (pairL u v : ℂ)) * infFourier f u := by
  have hfc : Continuous f := hf.continuous
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hf'c : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hf's : HasCompactSupport (fun y => fderiv ℝ f y v) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin n → Cinf E) →L[ℝ] ℂ => L v) rfl
  have hgc := continuous_kernel u
  have h1 : Integrable (fun x => fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hf'c.mul hgc).integrable_of_hasCompactSupport hf's.mul_right
  have h2 : Integrable (fun x => f x * fderiv ℝ (fun y => (𝐞 (-pairL u y) : ℂ)) x v) (infMeasure E n) := by
    simp only [fderiv_kernel]
    exact (hfc.mul (continuous_const.mul hgc)).integrable_of_hasCompactSupport hs.mul_right
  have h3 : Integrable (fun x => f x * (𝐞 (-pairL u x) : ℂ)) (infMeasure E n) :=
    (hfc.mul hgc).integrable_of_hasCompactSupport hs.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3 (fun x _ => hd x)
    (fun x _ => (hasFDerivAt_kernel u x).differentiableAt)
  simp only [fderiv_kernel] at key
  have e : ∫ x, f x * (-(2 * π * I * (pairL u v : ℂ)) * (𝐞 (-pairL u x) : ℂ)) ∂infMeasure E n =
      -(2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  show ∫ x, fderiv ℝ f x v * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n =
    (2 * π * I * (pairL u v : ℂ)) * ∫ x, f x * (𝐞 (-pairL u x) : ℂ) ∂infMeasure E n
  linear_combination key - e


open Classical in
def dirv (k : Fin n × InfinitePlace E × Bool) : Fin n → Cinf E :=
  Pi.single k.1 (Pi.single k.2.1 (if k.2.2 then I else 1))

theorem pairL_dirv (u : Fin n → Cinf E) (k : Fin n × InfinitePlace E × Bool) :
    pairL u (dirv k) = 2 * ((if k.2.2 then I else 1) * u k.1 k.2.1).re := by
  classical
  obtain ⟨i, w, b⟩ := k
  rw [pairL_apply, Finset.sum_eq_single i, Finset.sum_eq_single w]
  · simp [dirv]
  · intro w' _ hw
    simp [dirv, Pi.single_apply, hw]
  · simp
  · intro j _ hj
    simp [dirv, Pi.single_apply, hj]
  · simp

theorem norm_le_sum_pairL (u : Fin n → Cinf E) : ‖u‖ ≤ ∑ k, |pairL u (dirv k)| := by
  have hcoord : ∀ i w, ‖u i w‖ ≤ |pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))| := by
    intro i w
    rw [pairL_dirv, pairL_dirv]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Complex.I_mul_re, abs_mul, abs_neg, abs_two]
    have := Complex.norm_le_abs_re_add_abs_im (u i w)
    nlinarith [abs_nonneg (u i w).re, abs_nonneg (u i w).im]
  have hS : ∑ k, |pairL u (dirv k)| =
      ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hS]
  have h0 : 0 ≤ ∑ i, ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
  refine (hcoord i w).trans ?_
  have hi := Finset.single_le_sum (f := fun i => ∑ w, (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun i _ => by positivity) (Finset.mem_univ i)
  have hw := Finset.single_le_sum (f := fun w => (|pairL u (dirv (i, w, false))| + |pairL u (dirv (i, w, true))|))
    (fun w _ => by positivity) (Finset.mem_univ w)
  exact hw.trans hi

end GlobalTheory.FourierDecay


open GlobalTheory.FourierDecay in
theorem GlobalTheory.fourier_decay_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (ι : Type)
    (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)),
    (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) →
    (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) →
    ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  intro E _ _ _ n ι w 𝒞 hC hD M
  induction M with
  | zero =>
    intro f hf
    obtain ⟨C, hC'⟩ := (hC f hf).2
    refine ⟨C, fun i u => ?_⟩
    rw [pow_zero, mul_one]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hC' i))
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖f i x * _‖ = ‖f i x‖
    rw [norm_mul, Circle.norm_coe, mul_one]
  | succ M ih =>
    intro f hf
    choose C hC' using fun k : Fin n × InfinitePlace E × Bool => ih _ (hD f hf (dirv k))
    obtain ⟨C₀, h₀⟩ := ih f hf
    refine ⟨C₀ + ∑ k, C k / (2 * π), fun i u => ?_⟩
    obtain ⟨hsm, hcs⟩ := (hC f hf).1 i
    have hrel : ∀ k, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * |pairL u (dirv k)| =
        ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
      intro k
      rw [infFourier_fderiv hsm hcs, norm_mul]
      have : ‖(2 * π * I * (pairL u (dirv k) : ℂ))‖ = 2 * π * |pairL u (dirv k)| := by
        simp [norm_mul, Complex.norm_real, abs_of_pos pi_pos]
      rw [this]
      field_simp
    have hN := norm_le_sum_pairL u
    have hA : 0 ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M := by positivity
    calc ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ (M + 1)
        = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ‖u‖ := by ring
      _ ≤ ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M + ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M * ∑ k, |pairL u (dirv k)| :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hN hA)
      _ = ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M +
            ∑ k, ‖infFourier (fun y => fderiv ℝ (f i) y (dirv k)) u‖ * (1 + ‖u‖) ^ M / (2 * π) := by
          rw [Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun k _ => hrel k)
      _ ≤ C₀ * w i + ∑ k, C k * w i / (2 * π) :=
          add_le_add (h₀ i u) (Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right (hC' k i u) (by positivity))
      _ = (C₀ + ∑ k, C k / (2 * π)) * w i := by
          rw [add_mul, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by ring
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.SatakeL

theorem isL_single_unrChar : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
      IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
        (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  intro hEx hLM hSC hZP hGL hBZ k _ _ _ _ _ x α hsat
  obtain ⟨𝔪, hL⟩ := hEx k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL

  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1

  have hlen : ∀ i, (Δ i).len = 1 := fun i =>
    (GlobalTheory.T.sphericalSegmentRep_length_one_unramified hLM hSC hZP hGL hBZ k (Δ i) (y i) (hseg i) (hsphy i)).1
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)

  have h1 : HasSupport x.rep (msupp 𝔪) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZP k 𝔪 x hL
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => GlobalTheory.SmGL.unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.T.supercuspidalSupport_unique_GL hGL hBZ hZP k x _ _ h1 h2
  have hsupp : msupp 𝔪 = Finset.univ.val.map fun i => (Δ i).first := by
    rw [msupp, ← hord.1, Multiset.bind_map]
    simp only [hms]
    exact Multiset.bind_singleton _ _
  rw [hsupp] at heq

  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.LocLanglands.SatakeL
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.hodgeTateJump_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  first | exact @GlobalTheory.Per.JumpRestrict.jump_restrict | exact GlobalTheory.Per.JumpRestrict.jump_restrict | (intros; apply GlobalTheory.Per.JumpRestrict.jump_restrict <;> assumption)
end
