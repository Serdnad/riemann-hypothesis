module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter Asymptotics

noncomputable section

namespace PolyGermPointPow

theorem coeff_eq_zero_of_isBigO {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by
  induction k with
  | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    have hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ) := (continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ
    have hk := ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hk
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
    · exact hk d hd
    rw [hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨c, hc⟩ := h.bound
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖ := by
      filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow,
        norm_norm, pow_succ] at ht
      have hp : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.mpr ht0) k
      exact le_of_mul_le_mul_left (by linarith) hp
    have h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖) :=
      ((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)

theorem eval_smul_of_isHomogeneous {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ}
    (hh : h.IsHomogeneous d) (t : ℂ) (v : σ → ℂ) : eval (t • v) h = t ^ d * eval v h :=
  _root_.UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous hh t v

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

def bigOIdeal (k : ℕ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧
    f =O[𝓝 w] fun z => ‖z - w‖ ^ k}
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  smul_mem' := by
    rintro c φ ⟨f, hf, hfO⟩
    obtain ⟨a, ha, hac⟩ := c.2
    refine ⟨a * f, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hac]; rfl
    · show (fun z => a z * f z) =O[𝓝 w] fun z => ‖z - w‖ ^ k
      simpa using (ha.continuousAt.tendsto.isBigO_one ℝ).mul hfO

theorem bigOIdeal_zero : bigOIdeal w 0 = ⊤ := by
  refine eq_top_iff.mpr fun φ _ => ?_
  obtain ⟨f, hf, hfφ⟩ := φ.2
  exact ⟨f, hfφ, by simpa using hf.continuousAt.tendsto.isBigO_one ℝ⟩

theorem pointIdeal_le_bigOIdeal_one : holGermPointIdeal w ≤ bigOIdeal w 1 := by
  intro φ hφ
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have h0 : f w = 0 := by
    have : (Germ.valueRingHom (x := w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ
    exact this
  refine ⟨f, hfφ, ?_⟩
  have := hf.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at this
  simpa using this.norm_right

theorem bigOIdeal_mul_le (a b : ℕ) : bigOIdeal w a * bigOIdeal w b ≤ bigOIdeal w (a + b) := by
  rw [Ideal.mul_le]
  rintro φ ⟨f, hf, hfO⟩ ψ ⟨g, hg, hgO⟩
  refine ⟨f * g, ?_, ?_⟩
  · rw [Subring.coe_mul, ← hf, ← hg]; rfl
  · show (fun z => f z * g z) =O[𝓝 w] fun z => ‖z - w‖ ^ (a + b)
    simpa [pow_add] using hfO.mul hgO

theorem pointIdeal_pow_le (k : ℕ) : holGermPointIdeal w ^ k ≤ bigOIdeal w k := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, bigOIdeal_zero]
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (pointIdeal_le_bigOIdeal_one w)).trans (bigOIdeal_mul_le w k 1)

theorem mem_pow_ker_of_isBigO {k : ℕ} {q : MvPolynomial σ ℂ}
    (hq : (fun z => eval z q) =O[𝓝 w] fun z => ‖z - w‖ ^ k) :
    q ∈ RingHom.ker (MvPolynomial.eval w) ^ k := by
  set q' := bind₁ (fun i => X i + C (w i)) q with hq'def
  have hev : ∀ y, eval y q' = eval (y + w) q := by
    intro y
    rw [hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]
    have hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w := by
      ext i
      simp only [map_add (f := _), eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]
    rw [hfun]
    rfl

  have hcomp : ∀ d < k, homogeneousComponent d q' = 0 := by
    intro d hd
    by_cases hdT : d ∈ Finset.range (q'.totalDegree + 1)
    swap
    · exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)
    refine MvPolynomial.funext fun v => ?_
    let P : Polynomial ℂ := ∑ e ∈ Finset.range (q'.totalDegree + 1),
      Polynomial.monomial e (eval v (homogeneousComponent e q'))
    have hP : ∀ t, P.eval t = eval (t • v + w) q := by
      intro t
      rw [← hev]
      conv_rhs => rw [← sum_homogeneousComponent q']

      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]
    have hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w) := by
      simpa using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ)
        (f := fun t : ℂ => t • v + w)
    have hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k := by
      simp_rw [hP]
      refine (hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))
      simp [norm_smul, mul_pow, mul_comm]
    have hc := coeff_eq_zero_of_isBigO hPO d hd
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finsupp.single_apply, Finset.sum_ite_eq', if_pos hdT] at hc
    simpa using hc
  have hmem : q' ∈ idealOfVars σ ℂ ^ k := by
    refine (mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_
    have := congrArg (AddMonoidAlgebra.coeff · x) (hcomp _ hx)
    simpa [coeff_homogeneousComponent, AddMonoidAlgebra.coeff] using this
  have hback : bind₁ (fun i => X i - C (w i)) q' = q := by
    rw [hq'def, bind₁_bind₁]
    have hfun : (fun i => bind₁ (fun i => X i - C (w i)) (X i + C (w i) : MvPolynomial σ ℂ)) = X := by
      funext i
      rw [map_add, bind₁_X_right, bind₁_C_right, sub_add_cancel]
    rw [hfun, bind₁_X_left, AlgHom.id_apply]
  have := Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem
  rw [Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback] at this
  rw [GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]
  simpa [Function.comp_def, bind₁_X_right] using this

end PolyGermPointPow

theorem PolyGermPointPow.proof : PolyGermPointPow.Statement := by
  intro σ _ w k q hq
  obtain ⟨f, hf, hfO⟩ := PolyGermPointPow.pointIdeal_pow_le w k hq
  have hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := hf
  exact PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem VarietyProjectionMass.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hD : ComplexSets.DiscriminantCover.Statement) (hL : LocalGraphProjectionMass.Statement) :
    VarietyProjectionMass.Statement := by
  intro n d J hJ hd U hU B hB
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨W, hW, hWfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame W hW
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := W.submatrix (I₀.orderEmbOfFin hI₀) id
  have hAfin : ComplexSets.IsFiniteProjection J A := by
    simpa using hWfin 0 (I₀.orderEmbOfFin hI₀).toEmbedding
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd hAfin
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| hAfin.injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    NullSmaller.proof n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ B ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B := by
    rintro z ⟨hz, hzB⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzB⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J W b hb I₀ hI₀ P
    (fun y hy x hx => (hP y hy).2.2 x hx)) U hU B hB
  have hGZ : G ∩ B ⊆ zeroSetEuc J ∩ B := Set.inter_subset_inter_left _ Set.inter_subset_left
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ B) :=
        measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] (G ∩ B) := by rw [hbad, zero_add]
    _ ≤ _ := hgood
    _ ≤ _ := by
      refine Finset.sum_le_sum fun s _ => mul_le_mul' (iSup_mono fun x => ?_)
        (measure_mono (Set.image_mono hGZ))
      exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hGZ hz.1, hz.2⟩)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace PrimeGermNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]

    rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
    map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem coeff_eq_zero_of_distinct_roots {N : ℕ} (c t : Fin N → ℂ) (ht : Function.Injective t)
    (hroot : ∀ m, ∑ j, c j * t m ^ (j : ℕ) = 0) : ∀ j, c j = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun j => j.elim0
  set Q : Polynomial ℂ := ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
  have hQe : ∀ s, Q.eval s = ∑ j, c j * s ^ (j : ℕ) := by
    intro s
    simp [Q, Polynomial.eval_finsetSum]
  have hdeg : Q.natDegree < Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun j _ => ?_)
      (Nat.sub_lt hN Nat.one_pos)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hQ : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q ht
    (fun m => by rw [hQe]; exact hroot m) hdeg
  intro j
  have hj := congrArg (fun q : Polynomial ℂ => q.coeff (j : ℕ)) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Fin.val_inj] at hj
  simpa using hj

theorem proof (hCover : PrimeGermCanonicalCover.Statement) : PrimeGermNullstellensatz.Statement := by
  intro σ _ w k p g hp hg hP hvan
  obtain ⟨d, A, ℓ, N, δ, hδ, hδP, hdiv, hsheet⟩ := hCover σ w k p hp hP
  obtain ⟨M, a, h, ha, hh, hrel⟩ := hdiv g hg

  have hoff : ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ j, a j y = 0 := by
    filter_upwards [hsheet _ (hrel.and hvan)] with y hy hδy
    obtain ⟨x, hx, hinj⟩ := hy hδy
    refine coeff_eq_zero_of_distinct_roots (fun j => a j y) (fun m => ℓ (x m)) hinj fun m => ?_
    obtain ⟨⟨hr, hv⟩, hpx, hAx⟩ := hx m
    have hg0 : g (x m) = 0 := hv hpx
    have h0 : δ (A (x m)) ^ M * g (x m) - ∑ j, a j (A (x m)) * ℓ (x m) ^ (j : ℕ) = 0 := by
      rw [hr]
      simp [hpx]
    rw [hg0, mul_zero, zero_sub, neg_eq_zero, hAx] at h0
    exact h0

  have hδne : ¬ (δ =ᶠ[𝓝 (A w)] 0) := by
    intro h0
    apply hδP
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    filter_upwards [(A.continuous.tendsto w).eventually h0] with z hz
    simpa using hz

  have hzero : ∀ᶠ y in 𝓝 (A w), ∀ j, a j y = 0 := by
    have hall : ∀ᶠ y in 𝓝 (A w), AnalyticAt ℂ δ y ∧ (∀ j, AnalyticAt ℂ (a j) y) ∧
        (δ y ≠ 0 → ∀ j, a j y = 0) :=
      hδ.eventually_analyticAt.and ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and hoff)
    obtain ⟨r, hr0, hrB⟩ := Metric.eventually_nhds_iff_ball.1 hall
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y₀ hy₀ j
    by_contra hne
    apply hδne
    have hnear : δ =ᶠ[𝓝 y₀] 0 := by
      have hcont : ContinuousAt (a j) y₀ := ((hrB y₀ hy₀).2.1 j).continuousAt
      filter_upwards [hcont.eventually_ne hne, Metric.isOpen_ball.mem_nhds hy₀] with y hy hyB
      by_contra hδy
      exact hy ((hrB y hyB).2.2 hδy j)
    have hon : AnalyticOnNhd ℂ δ (Metric.ball (A w) r) := fun y hy => (hrB y hy).1
    have hEq := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hy₀ hnear
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y hy using hEq hy

  have hrel' : ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z = ∑ i, h i z * p i z := by
    filter_upwards [hrel, (A.continuous.tendsto w).eventually hzero] with z hz hz0
    rw [← hz]
    simp [hz0]
  have hδA : AnalyticAt ℂ (fun z => δ (A z)) w := hδ.comp (A.analyticAt w)
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  let Dg : holGerms w := ⟨((fun z => δ (A z) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hδA, rfl⟩
  have hmem : Dg ^ M * G ∈ holGermIdeal w p := by
    refine mem_holGermIdeal_of_eq hp hh _ ?_
    rw [show ((Dg ^ M * G : holGerms w) : Germ (𝓝 w) ℂ) =
        (((fun z => δ (A z)) ^ M * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) by
      rw [Germ.coe_mul, Germ.coe_pow]
      rfl]
    exact Germ.coe_eq.2 (hrel'.mono fun z hz => by simpa using hz)
  have hDg : Dg ∉ holGermIdeal w p := by
    intro hD
    obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hD
    exact hδP ⟨h', hh', Germ.coe_eq.1 e⟩
  have hG : G ∈ holGermIdeal w p := by
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact absurd (hP.mem_of_pow_mem M h1) hDg
    · exact h1
  obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hG
  exact ⟨h', hh', Germ.coe_eq.1 e⟩

end PrimeGermNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ne_of_mem_euclBall_diff {n : ℕ} {x z : Fin n → ℂ} {r s : ℝ} (hr : 0 < r)
    (hz : z ∈ euclBall x s \ euclBall x r) : z ≠ x := by
  rintro rfl
  exact hz.2 (mem_euclBall_self z hr)

def RegLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      r ^ (2 * d) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) -
        s ^ (2 * d) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) =
      r ^ (2 * d) * s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end
