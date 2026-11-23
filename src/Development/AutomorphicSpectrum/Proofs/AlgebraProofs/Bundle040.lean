module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbFrob
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle022
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbAflat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle036
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_one_series_in_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p :=
  PositivityTheory.HtPt.Cb.first_power_char_p

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g hL' hSE
  obtain ⟨hf, hfg, hg, hL, hL''⟩ := hSE
  have hsub := GlobalTheory.T.sub_and_quotient_bundles K C V' L' (LinearMap.range f) hL'
  obtain ⟨e1, he1⟩ : ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ x, (e x : V') = f x :=
    ⟨LinearEquiv.ofInjective f hf, fun x => by simp⟩
  have hker : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  obtain ⟨e2, he2⟩ : ∃ e : (V' ⧸ LinearMap.range f) ≃ₗ[K] V'',
      ∀ y, e (Submodule.Quotient.mk y) = g y :=
    ⟨(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective g hg),
      fun y => by simp [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]⟩
  have hc1 : ∀ (i : C.I) (x : LinearMap.range f),
      x ∈ GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f) i ↔ e1.symm x ∈ L i := by
    intro i x
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.sub, AddSubgroup.mem_comap]
    rw [hL i, ← he1, LinearEquiv.apply_symm_apply]
    exact Iff.rfl
  have hc2 : ∀ (i : C.I) (z : V' ⧸ LinearMap.range f),
      z ∈ GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f) i ↔ e2 z ∈ L'' i := by
    intro i z
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.quot]
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h2 : e2 (Submodule.Quotient.mk y) ∈ L'' i := by
        rw [he2]
        exact (hL'' i (g y)).2 ⟨y, hy, rfl⟩
      exact h2
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hL'' i _).1 hz
      refine ⟨y, hy, e2.injective ?_⟩
      have h3 : e2 (Submodule.Quotient.mk y) = e2 z := by rw [he2, hyz]
      exact h3
  obtain ⟨hLb, hdL⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (LinearMap.range f) V
    (GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f)) L e1.symm hsub.1 hc1
  obtain ⟨hL''b, hdL''⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (V' ⧸ LinearMap.range f) V''
    (GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f)) L'' e2 hsub.2 hc2
  refine ⟨hLb, hL''b, ?_⟩
  rw [GlobalTheory.T.degree_additive_sub_quotient K C V' L' (LinearMap.range f) hL']
  unfold GlobalTheory.CompanionTheory.Ar.Crv.subDeg
  rw [hdL, hdL'']

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.augmentation_length_colength_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  first | exact @PositivityTheory.HtPt.Ra.cnt | exact PositivityTheory.HtPt.Ra.cnt
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  first | exact @PositivityTheory.HtPt.Pmono.r_mono | exact PositivityTheory.HtPt.Pmono.r_mono
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @PositivityTheory.HtPt.Rb.flag_D | exact PositivityTheory.HtPt.Rb.flag_D
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.unit_ratio_same_divisor_multiplicities : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq | exact GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.unitRatio_divisor_cycle_eq <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

def kerFil {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]
    (a : S → w.valuationSubring) (r : ℕ) (g : S → (Fin r → C) →ₗ[C] W) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {f | f ∈ freeLattice a r ∧ ∀ s, g s (f s) = 0}
  zero_mem' := ⟨zero_mem _, fun s => by simp⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, fun s => by simp [hx.2 s, hy.2 s]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun s => by
    have e : (c • f) s = (c : C) • f s := rfl
    rw [e, map_smul, hf.2 s, smul_zero]⟩

def eigCoord {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) : (Fin N → C) →ₗ[C] M :=
  Fintype.linearCombination C (fun j => HT.eigProj ρ s (t j))

theorem eigCoord_apply {E : Type} [Field E] [NumberField E] {C M : Type} [Field C] [AddCommGroup M] [Module C M]
    (ρ : 𝓞 E →+* Module.End C M) {N : ℕ} (t : Fin N → M) (s : E →+* C) (y : Fin N → C) :
    eigCoord ρ t s y = ∑ j, y j • HT.eigProj ρ s (t j) := by
  simp [eigCoord, Fintype.linearCombination_apply]

def TargetO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (ν : Valuation C ℝ≥0)
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ),
    (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) →
    (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ ν.valuationSubring) →
    Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) →
    (∀ a, bar (bar a) = a) →
    ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module ν.valuationSubring W]
      [IsScalarTower ν.valuationSubring C W] [FiniteDimensional C W]
      (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
      (HV : Submodule ν.valuationSubring (W × Module.Dual C W)) (Lie : Submodule ν.valuationSubring W)
      (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W)
      (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C),
      (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) →
      HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars ν.valuationSubring) = Lie →
      (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap ν.valuationSubring C).range) →
      HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) →
      LinearIndependent C v → Submodule.span ν.valuationSubring (Set.range v) = HT.eigSub ρ σ Lie →
      LinearIndependent C w → Submodule.span ν.valuationSubring (Set.range w) = HT.eigSub ρ σ' Lie →
      IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) →
      Submodule.span ν.valuationSubring (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV →
      ∃ ε : (ν.valuationSubring)ˣ, A.det = algebraMap ν.valuationSubring C ε * γ

end GlobalTheory.CompanionTheory.Ar.Flat.ExG
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section LevelIndex

variable {R : Type} [Ring R] {L : Type} [AddCommGroup L] [Module R L]

def multiplesSub (L : Type) [AddCommGroup L] (N : ℕ) : AddSubgroup L := (nsmulAddMonoidHom (α := L) N).range

theorem finite_quot_multiplesSub [Module.Finite ℤ L] {N : ℕ} (hN : 0 < N) :
    Finite (L ⧸ multiplesSub L N) := by
  have : Module.Finite ℤ (L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) := inferInstance
  have htors : Module.IsTorsion ℤ (L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) := by
    intro x
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show (N : ℤ) • (Submodule.Quotient.mk y : L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  exact Module.finite_of_fg_torsion (M := L ⧸ (AddSubgroup.toIntSubmodule (multiplesSub L N))) htors

def modAct (N : ℕ) : (L ≃ₗ[R] L) →* Function.End (L ⧸ multiplesSub L N) where
  toFun γ := ⇑(QuotientAddGroup.map (multiplesSub L N) (multiplesSub L N)
    (γ.toLinearMap.toAddMonoidHom) (by
      rintro _ ⟨e, rfl⟩
      exact ⟨γ e, by simp⟩))
  map_one' := by
    funext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rfl
  map_mul' a b := by
    funext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rfl

theorem modAct_mk (N : ℕ) (γ : L ≃ₗ[R] L) (a : L) :
    modAct N γ (a : L ⧸ multiplesSub L N) = ((γ a : L) : L ⧸ multiplesSub L N) := rfl

def modKer (R : Type) [Ring R] (L : Type) [AddCommGroup L] [Module R L] (N : ℕ) : Subgroup (L ≃ₗ[R] L) :=
  (modAct (R := R) (L := L) N).toHomUnits.ker

theorem modKer_finiteIndex [Module.Finite ℤ L] {N : ℕ} (hN : 0 < N) :
    (modKer R L N).FiniteIndex := by
  have := finite_quot_multiplesSub (L := L) hN
  have : Finite (Function.End (L ⧸ multiplesSub L N)) := inferInstanceAs (Finite (_ → _))
  exact Subgroup.finiteIndex_ker _

theorem exists_of_mem_modKer {N : ℕ} {γ : L ≃ₗ[R] L} (h : γ ∈ modKer R L N) (a : L) :
    ∃ e, γ a = a + N • e := by
  have h1 : modAct N γ = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.1 h)
    simpa using this
  have h2 := congrFun h1 (a : L ⧸ multiplesSub L N)
  rw [modAct_mk] at h2
  have h3 : ((γ a : L) : L ⧸ multiplesSub L N) = (a : L ⧸ multiplesSub L N) := h2
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 h3.symm
  refine ⟨e, ?_⟩
  have he' : N • e = -a + γ a := he
  rw [he']
  abel

end LevelIndex

def levelGrp {E : Type} [Field E] [NumberField E] {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | (∀ a b, form (γ a) (γ b) = form a b) ∧
    (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e}
  one_mem' := ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩
    · show form (γ (δ a)) (γ (δ b)) = form a b
      rw [h1, k1]
    · obtain ⟨e, he⟩ := k2 a ha
      obtain ⟨e', he'⟩ := h2 a ha
      refine ⟨e' + γ e, ?_⟩
      show γ (δ a) = _
      rw [he, map_add (f := _), he', map_nsmul, smul_add, add_assoc]
    · obtain ⟨e, he⟩ := k3 a
      obtain ⟨e', he'⟩ := h3 a
      refine ⟨e' + γ e, ?_⟩
      show γ (δ a) = _
      rw [he, map_add (f := _), he', map_nsmul, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨h1, h2, h3⟩
    have hinv : ∀ a, γ (γ⁻¹ a) = a := fun a => γ.apply_symm_apply a
    refine ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩
    · have := h1 (γ⁻¹ a) (γ⁻¹ b)
      rw [hinv, hinv] at this
      exact this.symm
    · have hmem : γ⁻¹ a ∈ I • (⊤ : Submodule (𝓞 E) Λ) := by
        refine Submodule.smul_induction_on ha ?_ ?_
        · intro r hr n _
          rw [map_smul]
          exact Submodule.smul_mem_smul hr trivial
        · intro x y hx hy
          rw [map_add (f := _)]
          exact add_mem hx hy
      obtain ⟨e, he⟩ := h2 _ hmem
      rw [hinv] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg]
      exact eq_add_neg_of_add_eq he.symm
    · obtain ⟨e, he⟩ := h3 (γ⁻¹ a)
      rw [hinv] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg]
      exact eq_add_neg_of_add_eq he.symm

theorem levelGrp_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite ℤ Λ] (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ), 0 < M → 0 < A → ∃ Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ), Γ ≤ autGrp form ∧ Γ.relIndex (autGrp form) ≠ 0 ∧ ∀ γ, γ ∈ Γ ↔ (∀ a b, form (γ a) (γ b) = form a b) ∧ (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e := by
  intro E _ _ _ Λ _ _ _ form I M A hM hA
  refine ⟨levelGrp form I M A, fun γ h => h.1, ?_, fun γ => Iff.rfl⟩
  have hfin := modKer_finiteIndex (R := 𝓞 E) (L := Λ) (Nat.mul_pos hM hA)
  have hle : modKer (𝓞 E) Λ (M * A) ⊓ autGrp form ≤ levelGrp form I M A := by
    rintro γ ⟨hk, ha⟩
    refine ⟨ha, fun a _ => ?_, fun a => ?_⟩
    · obtain ⟨e, he⟩ := exists_of_mem_modKer hk a
      exact ⟨A • e, by rw [he, mul_smul]⟩
    · obtain ⟨e, he⟩ := exists_of_mem_modKer hk a
      exact ⟨M • e, by rw [he, mul_comm, mul_smul]⟩
  have h0 : (modKer (𝓞 E) Λ (M * A) ⊓ autGrp form).relIndex (autGrp form) ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  intro h
  have hd := Subgroup.relIndex_dvd_of_le_left (autGrp form) hle
  rw [h] at hd
  exact h0 (Nat.eq_zero_of_zero_dvd hd)

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

theorem _root_.GlobalTheory.T.quotient_of_affine_chart_cover : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.log_gap_measurable_scale_stable : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
  Measurable (logGap h u) ∧ ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.measurable_fibre_count_over : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
  Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.ae_polynomial_nonvanishing_rows : ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
  ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero <;> assumption)
end
