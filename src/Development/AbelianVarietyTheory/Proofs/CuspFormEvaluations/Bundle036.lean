module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphy
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle021

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_jet_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  first | exact @GlobalTheory.AnValJetEx.exists_gen_jetRd | exact GlobalTheory.AnValJetEx.exists_gen_jetRd | (intros; apply GlobalTheory.AnValJetEx.exists_gen_jetRd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphic_generator_reading_automorphy : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by
  first | exact @GlobalTheory.AnValGenRd.exists_reading | exact GlobalTheory.AnValGenRd.exists_reading | (intros; apply GlobalTheory.AnValGenRd.exists_reading <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

private theorem star_hermForm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (z w : Fin g → ℂ) : star (hermForm Hm z w) = hermForm Hm w z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← herm.apply j i, star_star]
  ring

private theorem norm_exp_neg_hermForm_mul_exp_hermForm_eq_one {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian) (r : ℝ)
    (x a : Fin g → ℂ) :
    ‖Complex.exp (-((r : ℂ) * hermForm Hm x a)) * Complex.exp ((r : ℂ) * hermForm Hm a x)‖ = 1 := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, ← star_hermForm_of_isHermitian Hm herm x a]
  simp

theorem thConst_liouville {g : ℕ} (lat : AddSubgroup (Fin g → ℂ))
    (span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ) (herm : Hm.IsHermitian)
    (k : ℤ) (x : Fin g → ℂ) (v : (Fin g → ℂ) → ℂ) (hv : Differentiable ℂ v)
    (hper : ∀ z, ∀ a ∈ lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm x a))) (z : Fin g → ℂ) :
    v z = v 0 * Complex.exp (-((k : ℂ) * Real.pi * hermForm Hm z x)) := by

  set c : ℝ := (k : ℝ) * Real.pi with hcdef
  have hcC : ((k : ℂ) * Real.pi) = (c : ℂ) := by rw [hcdef]; push_cast; ring
  simp only [hcC] at hper ⊢
  set f : (Fin g → ℂ) → ℂ := fun y => v y * Complex.exp ((c : ℂ) * hermForm Hm y x) with hf
  have hlin : ∀ y a : Fin g → ℂ, hermForm Hm (y + a) x = hermForm Hm y x + hermForm Hm a x := fun y a => by
    simp [hermForm, add_dotProduct]
  have hfd : Differentiable ℂ f := by
    refine hv.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    simp only [hermForm, dotProduct]
    fun_prop
  have hperf : ∀ y, ∀ a ∈ lat, ‖f (y + a)‖ = ‖f y‖ := by
    intro y a ha
    have e1 : f (y + a) = (v y * Complex.exp ((c : ℂ) * hermForm Hm y x)) *
        (Complex.exp (-((c : ℂ) * hermForm Hm x a)) * Complex.exp ((c : ℂ) * hermForm Hm a x)) := by
      simp only [hf, hper y a ha, hlin, mul_add, Complex.exp_add]
      ring
    rw [e1, norm_mul, norm_exp_neg_hermForm_mul_exp_hermForm_eq_one Hm herm c x a, _root_.mul_one]

  obtain ⟨s, hsl, hss, hli⟩ := exists_linearIndependent ℝ (lat : Set (Fin g → ℂ))
  rw [span] at hss
  let b : Module.Basis s ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hss.ge)
  have : Finite s := Module.Finite.finite_basis b
  letI : Fintype s := Fintype.ofFinite s
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (ZSpan.fundamentalDomain_isBounded b).closure
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hfd.continuous.continuousOn
  have hmem : ∀ y, y - ZSpan.fract b y ∈ lat := by
    intro y
    rw [ZSpan.fract_apply, sub_sub_cancel]
    have h1 : Submodule.span ℤ (Set.range b) ≤ lat.toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [b, Module.Basis.mk_apply] using hsl i.2
    exact h1 (ZSpan.floor b y).2
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h2 := hperf (ZSpan.fract b y) _ (hmem y)
    rw [add_sub_cancel] at h2
    rw [h2]
    exact hM _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b y))
  have h0 := hfd.apply_eq_apply_of_bounded hbd z 0
  have hz0 : hermForm Hm 0 x = 0 := by simp [hermForm]
  simp only [hf, hz0, mul_zero, Complex.exp_zero, _root_.mul_one] at h0
  rw [← h0, _root_.mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, _root_.mul_one]

private theorem fac_zpow_mul_fac_add_zpow_neg_eq_exp {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (k : ℤ) (x : Fin g → ℂ) {a : Fin g → ℂ} (ha : a ∈ Φ.lat) (z : Fin g → ℂ) :
    Φ.fac a z ^ k * Φ.fac a (x + z) ^ (-k) = Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
  have hχ : Φ.χ a ≠ 0 := by
    intro h
    have h1 := Φ.χ_norm a ha
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hne : Φ.fac a (x + z) ≠ 0 := mul_ne_zero hχ (Complex.exp_ne_zero _)
  have hq : Φ.fac a z = Φ.fac a (x + z) * Complex.exp (-((Real.pi : ℂ) * hermForm Φ.Hm x a)) := by
    simp only [AnFr.fac, hermForm, add_dotProduct]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hq, mul_zpow, zpow_neg, mul_comm (Φ.fac a (x + z) ^ k), _root_.mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero _ hne), _root_.mul_one, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_thConst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ), U.pt = Φ.e x → ∃ c : ℂ, c ≠ 0 ∧ Φ.ThConst k U x c := by
  intro S A _ _ L x0 g Φ k U x hU

  have hs : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ snd (Over.mk x0) A = t := by
    intro t
    simp [ptSecT]
  have ht : ∀ t : Over.mk x0 ⟶ A, ptSecT A t ≫ translPt A U.pt = U.pt * t := by
    intro t
    simp only [ptSecT, translPt, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, Category.id_comp]
  have hh : IsHolFam (g := g) (fun z => (ptSecT A (Φ.e z)).left) := by
    have h := isHolFam_pullback_lift S (Over.mk x0).left A.left (Over.mk x0).hom A.hom g (fun _ => 𝟙 _)
      (fun z => (Φ.e z).left) x0 (fun _ => Category.id_comp _) (fun z => Over.w (Φ.e z))
      (isHolFam_const (g := g) _) Φ.hol
    exact h
  have hdiff : ∀ i : Fin 2, Differentiable ℂ ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i) :=
    Fin.forall_fin_two.2 ⟨differentiable_id, (differentiable_const x).add differentiable_id⟩
  have hq : ∀ (z : Fin g → ℂ) (i : Fin 2), (ptSecT A (Φ.e z)).left ≫
      (![(snd (Over.mk x0) A).left, (translPt A U.pt).left] : Fin 2 → _) i =
      (Φ.e ((![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z)).left := by
    intro z
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left
      rw [← Over.comp_left, hs]
    · show (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left
      rw [← Over.comp_left, ht, hU, Φ.e_add]

  obtain ⟨v, hvd, hv0, hvR, -, hvP⟩ := GlobalTheory.AnValGenRd.exists_reading S A L x0 g Φ (Over.mk x0 ⊗ A).left (Fin 2)
    ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ U.isGen g
    (fun z => (ptSecT A (Φ.e z)).left) ![fun z => z, fun z => x + z] hh hdiff hq
  have hper : ∀ z, ∀ a ∈ Φ.lat, v (z + a) = v z * Complex.exp (-((k : ℂ) * Real.pi * hermForm Φ.Hm x a)) := by
    intro z a ha
    have hqa : (ptSecT A (Φ.e (z + a))).left = (ptSecT A (Φ.e z)).left := by
      rw [Φ.e_add, (Φ.e_ker a).2 ha, _root_.mul_one]
    have h := hvP z (z + a) (fun _ => a) hqa (Fin.forall_fin_two.2 ⟨⟨ha, rfl⟩, ⟨ha, (add_assoc x z a).symm⟩⟩)
    rw [Fin.prod_univ_two] at h
    rw [h, ← fac_zpow_mul_fac_add_zpow_neg_eq_exp Φ k x ha z]
    rfl
  refine ⟨v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2),
    mul_ne_zero (hv0 0) (Complex.exp_ne_zero _), hU, fun z => ?_⟩
  have hvz : v 0 * Complex.exp ((k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2) * fock Φ.Hm k x (fun _ => 1) z = v z := by
    rw [thConst_liouville Φ.lat Φ.span Φ.Hm Φ.herm k x v hvd hper z]
    simp only [fock, _root_.mul_one]
    rw [_root_.mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hp : (fun i : Fin 2 => (![fun z => z, fun z => x + z] : Fin 2 → (Fin g → ℂ) → Fin g → ℂ) i z) = ![z, x + z] := by
    funext i
    fin_cases i <;> rfl
  have hR := hvR z
  rw [hp] at hR
  rw [hvz]
  exact hR

end GlobalTheory.AnVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.jetReading_linearSubstitution_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  first | exact @GlobalTheory.JetLinSub.jetRd_linSubst | exact GlobalTheory.JetLinSub.jetRd_linSubst | (intros; apply GlobalTheory.JetLinSub.jetRd_linSubst <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_isHolFam_comp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam fun v => e (A v) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

theorem chart_holTo_of_isHolFam {Y : Scheme.{0}} {N : ℕ} {e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolFam e) :
    IsHolTo Set.univ e := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and]
  exact ⟨h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem AnPt.chart_jx_left (m : ℕ) : (Φ.jx m).left = jetPt (fun z => (Φ.e z).left) Φ.hol m := rfl

theorem AnPt.chart_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem AnPt.chart_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ Φ.jx (m + 1) =
      Φ.jx m := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, Φ.chart_jx_left]
  exact jetPt_trunc _ _ m

theorem AnPt.chart_zero (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ Φ.jx m = 1 := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, one_left'']
  have h1 := jetPt_aug (fun z => (Φ.e z).left) Φ.hol m
  refine h1.trans ?_
  show (Φ.e 0).left = _
  rw [Φ.chart_e_zero, one_left'']
  show y.x ≫ _ = (spMap (algebraMap ℂ ℂ) ≫ y.x) ≫ _
  rw [Algebra.algebraMap_self, spMap]
  simp

theorem AnPt.chart_act (m : ℕ) (a : 𝓞 E) :
    Φ.jx m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ Φ.jx m := by
  ext1
  rw [Over.comp_left, Over.comp_left, Φ.chart_jx_left]
  have hlin : ∀ z, (Φ.e z).left ≫ (Xo.univ.t.act.act a).left = (Φ.e (fun k => ty k (a : E) * z k)).left := by
    intro z
    rw [← Over.comp_left, ← Φ.lin a z]
    rfl
  have hol' := isHolFam_comp (fun z => (Φ.e z).left) Φ.hol (Xo.univ.t.act.act a).left
  rw [jetPt_comp (fun z => (Φ.e z).left) Φ.hol _ _ hol' (fun z => rfl)]
  haveI : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m)
      (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2))))
      (fun _ => sub_const_mem_orig _)
  symm
  refine jetPt_precomp (fun z => (Φ.e z).left) _ Φ.hol hol' ?_ m _ ?_
  · show (Φ.e 0).left ≫ _ = (Φ.e 0).left
    rw [hlin]; congr 2; funext k; simp
  · intro U hU f
    change jetSubstP m _ (jetOf m _) = _
    rw [jetSubstP_anAct, ← jetOf_scale m _ (contDiffAt_val _ Φ.hol hU f)]
    congr 1
    funext z
    show valAt' (Φ.e _).left U f = valAt' ((Φ.e z).left ≫ _) U f
    rw [hlin]

theorem AnPt.chart_tan (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (fun z => (Φ.e z).left) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        Φ.jx (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  classical
  let v : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j =>
    homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ Φ.jx (0 + 1)
  let u : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j => epsHom y.x (if j = j0 then 1 else 0) ≫ v j
  refine ⟨u, fun j => by simp [u, v, epsHom], ?_⟩
  have hone : ∀ j, j ≠ j0 → u j = 1 := by
    intro j hj
    ext1
    simp only [u, v, if_neg hj, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left]
    rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug, one_left'']
    show spMap _ ≫ (Φ.e 0).left = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y.x) ≫ _
    rw [Φ.chart_e_zero, one_left'', Category.assoc]
    rfl
  have hprod : (List.ofFn u).prod = u j0 := by
    rw [List.prod_ofFn, Finset.prod_eq_single j0 (fun j _ hj => hone j hj) (by simp)]
  rw [hprod]
  simp only [u, v, if_pos rfl, ite_true, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left,
    epsMul_one]
  rw [show spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ from by simp [spMap]]
  exact (Category.id_comp _).trans (jetPt_tan (fun z => (Φ.e z).left) Φ.hol ((0 : Fin 1), j0) vt hd)

theorem AnPt.chart_pair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (Φ.e (anPr 0 v)).left (Φ.e (anPr 1 v)).left
        ((Over.w (Φ.e (anPr 0 v))).trans (Over.w (Φ.e (anPr 1 v))).symm) :=
  chart_holTo_of_isHolFam (isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom Xo.univ.t.G.hom (2 * g)
    (fun v => (Φ.e (anPr 0 v)).left) (fun v => (Φ.e (anPr 1 v)).left) y.x
    (fun v => Over.w (Φ.e (anPr 0 v))) (fun v => Over.w (Φ.e (anPr 1 v)))
    (chart_isHolFam_comp_clm _ Φ.hol (anPr 0)) (chart_isHolFam_comp_clm _ Φ.hol (anPr 1)))

theorem AnPt.chart_law (m : ℕ) :
    Formalism.L2.Pj.homAt y.x
      (jetSubstP (S := ℂ) m fun p : Fin 1 × Fin g => psTrunc m (PullbackSections.addF ℂ g p.2)) ≫ Φ.jx m =
      jpt y g Φ.jx m (0 : Fin 2) * jpt y g Φ.jx m (1 : Fin 2) :=
  jets_law y.x Φ.e Φ.hol Φ.jx (fun _ => rfl) Φ.e_add Φ.chart_pair m

theorem anPt_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el),
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx :=
  fun _ _ _ _ _ _ _ _ _ _ _ y _ _ el Φ =>
    { zero := fun m => Φ.chart_zero m
      trunc := fun m => Φ.chart_trunc m
      law := fun m => Φ.chart_law m
      act := fun m a => Φ.chart_act m a
      tan := fun ℓ => Φ.chart_tan (el.symm ℓ) (y.u ℓ.1 ℓ.2) (Φ.der ℓ)
      basis := fun v => basis_single el v }

end GlobalTheory.AnVal
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RawChartBaseChange

theorem isCanonGauge_mapFB {S S' : Type} [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S']
    (ψ : S →+* S') {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB S d O)
    (h : Germ.PS S 2 d) (hh : B.IsCanonGauge S h) :
    (FBMap.mapFB ψ B).IsCanonGauge S' (MvPowerSeries.map ψ h) := by
  letI : Algebra S S' := ψ.toAlgebra
  have H : B.IsCanonGauge S' (MvPowerSeries.map ψ h) :=
    GaugeBaseChange.isCanonGauge_map B (Algebra.ofId S S') hh
  have hK : ∀ {n : ℕ} (f : Germ.PS S n d),
      Germ.FB.toK S' (MvPowerSeries.map ψ f : Germ.PS S' n d) = Germ.FB.toK S' f := by
    intro n f
    ext m
    rfl
  have hF : (FBMap.mapFB ψ B).FK S' = B.FK S' := funext fun i => hK (B.G.F i)
  have hA : ∀ a, (FBMap.mapFB ψ B).actK S' a = B.actK S' a :=
    fun a => funext fun i => hK (B.A.act a i)
  refine ⟨H.ax0, H.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK B.ph1).trans H.ph1
  · rw [hF]; exact (hK B.ph2).trans H.ph2
  · exact (hK B.sy).trans H.sy
  · rw [hA, hA]; exact (hK (B.ad a)).trans (H.ad a)

end GlobalTheory.RawChartBaseChange

namespace GlobalTheory

theorem rawChart_baseChange : RawBCSt := by
  intro E _ _ _ H Dw l Xo c _ S S' _ _ _ _ _ _ ψ x0 u C
  obtain ⟨e', hg, hc, -⟩ := GlobalTheory.T.exists_rawChart_frames_baseChange E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
    (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e C.frame.gen
  have hG := GlobalTheory.T.rawChart_baseChange_rig_germ_alt E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
    (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e e' C.frame.gen hg hc
    C.wP C.prim.1
  refine ⟨FBMap.mapFB (ψ : S →+* S') C.B, fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m, e',
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, ?_, ?_,
    RawChartBaseChange.isCanonGauge_mapFB _ C.B C.h C.gauge, hG.1 C.rig0, hG.2⟩
  · exact GlobalTheory.T.isRawChart_baseChange_jetPoints E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
      (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) u C.uvec C.chart
  · exact GlobalTheory.T.isFrame_rawChart_baseChange E H Dw l Xo S S' (ψ : S →+* S') x0 C.d C.B.G.F C.B.A.act C.x
      (fun m => rjBC (ψ : S →+* S') x0 C.d m 1 ≫ C.x m) (fun _ => rfl) C.e e' C.frame.gen hg hc
      _ _ _ _ C.frame

end GlobalTheory
end
