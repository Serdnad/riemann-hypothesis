module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle035
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle204
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle203
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.CoshMul

theorem bump_hasCompactSupport {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc ?_
  intro t ht
  apply h.2.2
  by_contra hh
  exact ht (abs_le.mp (not_lt.mp hh))

theorem bump_mul_integrable {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fun t => (g t : ℂ) * f t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp h.1.continuous).mul hf
  · exact ((bump_hasCompactSupport h).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right

theorem continuous_cosh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.cosh ((s : ℂ) * a)) :=
  Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_sinh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.sinh ((s : ℂ) * a)) :=
  Complex.continuous_sinh.comp (Complex.continuous_ofReal.mul continuous_const)

theorem bump_sinh_integral {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.sinh ((s : ℂ) * a) = 0 := by
  have h1 := integral_neg_eq_self (fun s : ℝ => (g s : ℂ) * Complex.sinh ((s : ℂ) * a)) volume
  have h2 : (fun s : ℝ => (g (-s) : ℂ) * Complex.sinh (((-s : ℝ) : ℂ) * a))
      = fun s : ℝ => -((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    funext s
    rw [h.2.1]
    push_cast
    rw [neg_mul, Complex.sinh_neg]
    ring
  simp only [h2] at h1
  rw [integral_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

theorem bump_cosh_shift {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) (t : ℝ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ∫ s : ℝ, (g s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
  have h1 : ∀ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ((g s : ℂ) * Complex.cosh ((s : ℂ) * a))
        + Complex.sinh ((t : ℂ) * a) * ((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    intro s
    push_cast
    rw [add_mul, Complex.cosh_add]
    ring
  simp_rw [h1]
  rw [integral_add ((bump_mul_integrable h (continuous_cosh_mul a)).const_mul _)
    ((bump_mul_integrable h (continuous_sinh_mul a)).const_mul _),
    integral_const_mul, integral_const_mul, bump_sinh_integral h a]
  simp

theorem conv_kernel_integrable {g g' : ℝ → ℝ} {T T' : ℝ} (h : IsBump g T) (h' : IsBump g' T')
    {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (Function.uncurry fun r t : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * f r)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have c1 := h.1.continuous
    have c2 := h'.1.continuous
    simp only [Function.uncurry_def]
    fun_prop
  · refine HasCompactSupport.intro
      (K := Set.Icc (-T - T') (T + T') ×ˢ Set.Icc (-T) T) (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨r, t⟩ hx
    simp only [Function.uncurry_apply_pair]
    by_cases ht : t ∈ Set.Icc (-T) T
    · have hr : r ∉ Set.Icc (-T - T') (T + T') := fun hr => hx ⟨hr, ht⟩
      have : T' < |r - t| := by
        by_contra hh
        have := abs_le.mp (not_lt.mp hh)
        exact hr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
      rw [h'.2.2 _ this]
      simp
    · have : T < |t| := by
        by_contra hh
        exact ht (abs_le.mp (not_lt.mp hh))
      rw [h.2.2 _ this]
      simp

theorem coshT_mul_coshT (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ) (h : IsBump g T) (h' : IsBump g' T') :
    coshT g c * coshT g' c = coshT (gconv g g') c := by
  unfold coshT gconv
  set a : ℂ := c ^ (1 / 2 : ℂ)
  have hc := continuous_cosh_mul a
  have e1 : ∀ r : ℝ, (((∫ t, g t * g' (r - t) : ℝ)) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ∫ t : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a) := by
    intro r
    rw [integral_mul_const, integral_complex_ofReal]
  simp_rw [e1]
  rw [integral_integral_swap (conv_kernel_integrable h h' hc)]
  have e2 : ∀ t : ℝ, ∫ r : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ((g t : ℂ) * Complex.cosh ((t : ℂ) * a)) * ∫ s : ℝ, (g' s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
    intro t
    have e3 := integral_add_right_eq_self
      (fun r : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)) (μ := volume) t
    rw [← e3]
    have e4 : ∀ s : ℝ, ((g t * g' (s + t - t) : ℝ) : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
        = (g t : ℂ) * ((g' s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)) := by
      intro s
      rw [add_sub_cancel_right]
      push_cast
      ring
    simp_rw [e4]
    rw [integral_const_mul, bump_cosh_shift h' a t]
    ring
  simp_rw [e2]
  rw [integral_mul_const]

end GlobalTheory.CompanionTheory.WaveMult.CoshMul
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem tilt_inj {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A)
    (ha : ∀ i, a (i + 1) ^ l = a i) (hb : ∀ i, b (i + 1) ^ l = b i)
    (hs : ∀ i, A.sharp (a i) = A.sharp (b i)) : a = b := by
  have hf : ∀ x y : A.A, (x - y) ^ l = x ^ l - y ^ l := fun x y => map_sub A.frob x y
  have key : ∀ j i, a i - b i = (a (i + j) - b (i + j)) ^ (l ^ j) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      rw [ih i, pow_succ' l j, pow_mul, hf, ← add_assoc, ha, hb]
  have hmem : ∀ j, a j - b j ∈ Ideal.span {A.pi} := by
    intro j
    rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, A.sharpMap_eq, A.sharpMap_eq,
      hs j, sub_self]
  have hdvd : ∀ i j, A.pi ^ j ∣ a i - b i := by
    intro i j
    have h1 : A.pi ∣ a (i + j) - b (i + j) := Ideal.mem_span_singleton.1 (hmem (i + j))
    rw [key j i]
    exact (pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans (pow_dvd_pow_of_dvd h1 _)
  have hH : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  funext i
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (hdvd i n)

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem untilt_mod_varpi_sq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest →
    ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧
      R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := by
  intro l _ A hA
  obtain ⟨t, ht⟩ := A.frob_bijective.2 A.pi
  have ht' : t ^ l = A.pi := ht
  have hpow : A.sharp t ^ l = (l : A.U) := by
    rw [← map_pow, ht', A.sharp_pi]
  refine ⟨A.sharp t, hpow, ?_⟩
  have hle : Ideal.span {(l : A.U) ^ 1} ≤ Ideal.span {A.sharp t ^ 2} := by
    rw [pow_one, ← hpow]
    exact Ideal.span_singleton_le_span_singleton.2
      (pow_dvd_pow _ (Fact.out : l.Prime).two_le)
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  let g : A.A →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    (Ideal.Quotient.factor hle).comp A.aToU1
  have hg : Function.Surjective g :=
    (Ideal.Quotient.factor_surjective hle).comp hsurj
  have hπ : ∀ a ∈ Ideal.span {A.pi}, g a = 0 := fun a ha => by
    rw [← hker] at ha
    change Ideal.Quotient.factor hle (A.aToU1 a) = 0
    rw [RingHom.mem_ker.1 ha, map_zero]
  let g' : A.A ⧸ Ideal.span {A.pi} →+* A.U ⧸ Ideal.span {A.sharp t ^ 2} :=
    Ideal.Quotient.lift _ g hπ
  have hg' : Function.Surjective g' := Ideal.Quotient.lift_surjective_of_surjective _ hπ hg
  exact ⟨(GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g' hg').2
      (GlobalTheory.CompanionTheory.ValQuot.valuation_comparable_quotient A.pi hA.2),
    (GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective g hg).1 hA.1⟩

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem exists_lim_of_dvd {R : Type*} [CommRing R] (p : R) [IsAdicComplete (Ideal.span {p}) R]
    (g : ℕ → R) (hg : ∀ n, p ^ n ∣ g (n + 1) - g n) : ∃ y, ∀ n, p ^ n ∣ g n - y := by
  have chain : ∀ m k, p ^ m ∣ g (m + k) - g m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : p ^ m ∣ g (m + k + 1) - g (m + k) :=
        (pow_dvd_pow p (Nat.le_add_right m k)).trans (hg (m + k))
      have := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) g (fun {m n} hmn => by
    rw [smodEq_span_singleton_pow_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (dvd_sub_comm).1 (chain m k))
  exact ⟨L, fun n => (smodEq_span_singleton_pow_iff _ _ _ _).1 (hL n)⟩

theorem isAdicComplete_quotient {R : Type*} [CommRing R] (p ξ : R)
    [IsAdicComplete (Ideal.span {p}) R] (h : ∀ (n : ℕ) (x : R), p ^ n ∣ ξ * x → p ^ n ∣ x) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
  have hH : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : ∀ n : ℕ, ∃ y z, a = ξ * y + p ^ n * z := by
      intro n
      have hd := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hx n)
      rw [sub_zero] at hd
      obtain ⟨c, hc⟩ := hd
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h0 : Ideal.Quotient.mk (Ideal.span {ξ}) (a - p ^ n * c') = 0 := by
        rw [map_sub, map_mul, map_pow, hc, sub_self]
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      exact ⟨y, c', by linear_combination hy⟩
    choose y z hyz using h1
    have hy : ∀ n, p ^ n ∣ y (n + 1) - y n := fun n =>
      h n _ ⟨z n - p * z (n + 1), by linear_combination hyz n - hyz (n + 1)⟩
    obtain ⟨Y, hY⟩ := exists_lim_of_dvd p y hy
    have hz : a - ξ * Y = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {p}) _ fun n => ?_
      rw [smodEq_span_singleton_pow_iff, sub_zero]
      obtain ⟨c, hc⟩ := hY n
      exact ⟨ξ * c + z n, by linear_combination hyz n + ξ * hc⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨Y, sub_eq_zero.1 hz⟩)
  have hP : IsPrecomplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) p}) (R ⧸ Ideal.span {ξ}) := by
    refine ⟨fun f hf => ?_⟩
    have step : ∀ (n : ℕ) (x : R), Ideal.Quotient.mk (Ideal.span {ξ}) x = f n →
        ∃ y, Ideal.Quotient.mk (Ideal.span {ξ}) y = f (n + 1) ∧ p ^ n ∣ y - x := by
      intro n x hx
      obtain ⟨c, hc⟩ := (smodEq_span_singleton_pow_iff _ _ _ _).1 (hf (Nat.le_succ n))
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨x - p ^ n * c', ?_, ⟨-c', by ring⟩⟩
      rw [map_sub, map_mul, map_pow, hx, ← hc]
      ring
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (f 0)
    let G : ∀ n, {x : R // Ideal.Quotient.mk (Ideal.span {ξ}) x = f n} := fun n =>
      Nat.rec ⟨x0, hx0⟩ (fun n x => ⟨(step n x.1 x.2).choose, (step n x.1 x.2).choose_spec.1⟩) n
    have hG : ∀ n, p ^ n ∣ (G (n + 1)).1 - (G n).1 := fun n => (step n _ (G n).2).choose_spec.2
    obtain ⟨y, hy⟩ := exists_lim_of_dvd p (fun n => (G n).1) hG
    refine ⟨Ideal.Quotient.mk _ y, fun n => ?_⟩
    rw [smodEq_span_singleton_pow_iff]
    have := map_dvd (Ideal.Quotient.mk (Ideal.span {ξ})) (hy n)
    rwa [map_pow, map_sub, (G n).2] at this
  exact { hH, hP with }

theorem isAdicComplete_U : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  intro l _ A
  have hc := isAdicComplete_quotient (l : A.W) A.xi (fun n x hx =>
    Ideal.mem_span_singleton.1 ((GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).2.2 n x (Ideal.mem_span_singleton.2 hx)))
  have e : (l : A.U) = Ideal.Quotient.mk (Ideal.span {A.xi}) (l : A.W) := (map_natCast A.th l).symm
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.perfectoid_xi_nonZeroDivisor : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧ ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} → x ∈ Ideal.span {(l : A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | exact GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular | (intros; apply GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.restrict_self_pullC_eq : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | exact GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | (intros; apply GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_union_le_site : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := by
  first | exact @GlobalTheory.CompanionTheory.ConeSite.wU_le_KS | exact GlobalTheory.CompanionTheory.ConeSite.wU_le_KS | (intros; apply GlobalTheory.CompanionTheory.ConeSite.wU_le_KS <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.integral_ring_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  first | exact @GlobalTheory.CompanionTheory.TiltFacts.obFacts | exact GlobalTheory.CompanionTheory.TiltFacts.obFacts | (intros; apply GlobalTheory.CompanionTheory.TiltFacts.obFacts <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTHodge

variable {l : ℕ} [Fact l.Prime]

def lineRep {K LL : FinExt l} (ψ : ↥(GK K) →* (↥LL.1)ˣ) :
    Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin 1) (Fin 1) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL.1).comp ψ))

def ltSeries {K : FinExt l} (π : ↥(OL K)) : PowerSeries ↥(OL K) :=
  PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card (↥(OL K) ⧸ Ideal.span {π})

def IsLTChar (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∃ (π : ↥(OL K)) (z : ℕ → Om l), Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def HasPeriods (P : LocPrime l) (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) : Prop :=
  ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ∃ y : P.R.BdR,
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      P.actQdR g y = algebraMap (Om l) P.R.BdR (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * y) ∧
    (μ = K.1.val → y ∈ (P.PD K).Fil 1 ∧ y ∉ (P.PD K).Fil 2) ∧
    (μ ≠ K.1.val → y ∈ (P.PD K).Fil 0 ∧ y ∉ (P.PD K).Fil 1)

end GlobalTheory.CompanionTheory.LTHodge
end
end
