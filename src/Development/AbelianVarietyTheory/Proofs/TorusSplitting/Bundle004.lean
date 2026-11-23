module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValClosure

theorem vV_eq_of_hasVal {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {x : FractionRing V} {n : ℤ} (h : ReciprocityTheory.ChartRestriction.G.DVR.HasVal ϖ x n) : vV V x = n := by
  obtain ⟨u, rfl⟩ := h
  have h1 : valV V (algebraMap V (FractionRing V) ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  have hle : ∀ w : V, valV V (algebraMap V (FractionRing V) w) ≤ 1 := fun w =>
    HeightOneSpectrum.valuation_le_one _ w
  have h2 : valV V (algebraMap V (FractionRing V) (u : V)) = 1 := by
    refine le_antisymm (hle _) ?_
    have h3 : valV V (algebraMap V (FractionRing V) (u : V)) *
        valV V (algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ valV V (algebraMap V (FractionRing V) (u : V)) * 1 := mul_le_mul' le_rfl (hle _)
      _ = _ := _root_.mul_one _
  rw [vV, map_mul, h2, _root_.mul_one, map_zpow₀, h1, WithZero.log_zpow, WithZero.log_exp]
  simp

theorem exists_valuation_closure : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v ∧ ∀ x : FractionRing V, x ≠ 0 → v (algebraMap _ _ x) = (((vV V x : ℤ) : ℚ) : WithTop ℚ) := by
  intro V _ _ _ ϖ hϖ
  obtain ⟨v, hv⟩ := GlobalTheory.exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure (FractionRing V))
  refine ⟨v, hv, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
  rw [vV_eq_of_hasVal hϖ hn]
  exact hv x n hn

end GlobalTheory.ValClosure
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem sum_cosetMin_ge_phiC_div_sq : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E), (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) → ∀ w₀ : 𝓞 E, (w₀ : E) + cj w₀ = 1 → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] (Q : X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X), (∀ a, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → (∀ a, 0 ≤ Q a) → ∀ (m : ℕ), 2 ≤ m → ∀ (n : ℕ) (y : Fin n → X), (∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m ^ 2 • t) → ∀ v : Fin n → WithTop ℚ, (∀ b (q : ℚ), (∀ χ, q ≤ (Q (m • χ + y b) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v b) → ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (m : ℝ) ^ 2 → (q : WithTop ℚ) ≤ ∑ b, v b := by
  intro E _ _ cj hcj w₀ hw X _ _ _ Q β hβQ hQnn m hm n y hgen v hv q hq
  have hβpos : ∀ a, 0 ≤ (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβQ a]
    have h' : (0 : ℝ) ≤ Q a := by exact_mod_cast hQnn a
    linarith
  choose z hz using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.etPoint_min Q hQnn (y b) m
  have hgen' : ∀ a : X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : X, a = u + m • t := fun a => by
    obtain ⟨u, hu, t, ht⟩ := hgen a
    exact ⟨u, hu, m • t, by rw [ht, smul_smul, pow_two]⟩
  have hspan := Formalism.MainNotions.ModuliIntegralCharts.H1.etSpan_holds E X m hm n y z hgen'
  have hphi := Formalism.MainNotions.ModuliIntegralCharts.H1.phiCSpan_holds E cj hcj X w₀ hw β hβpos n (fun b => y b + m • z b) hspan
  have hsum : Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ ∑ b, (Q (y b + m • z b) : ℝ) := by
    refine hphi.trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    have h := Formalism.MainNotions.ModuliIntegralCharts.H1.two_mul_form_half_unit hcj w₀ hw β (y b + m • z b)
    rw [hβQ] at h
    linarith
  have hpt : ∀ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤ v b := by
    intro b
    refine hv b _ fun z' => ?_
    have h : (Q (y b + m • z b) : ℚ) ≤ (Q (m • z' + y b) : ℚ) := by
      rw [add_comm (m • z')]
      exact_mod_cast hz b z'
    exact div_le_div_of_nonneg_right h (by positivity)
  have hR : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hqR : (q : ℝ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rw [← Finset.sum_div]
    exact hq.trans (div_le_div_of_nonneg_right hsum hR.le)
  have hqQ : q ≤ ∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) := by exact_mod_cast hqR
  calc ((q : ℚ) : WithTop ℚ) ≤ ((∑ b, (Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) :=
        WithTop.coe_le_coe.2 hqQ
    _ = ∑ b, (((Q (y b + m • z b) : ℚ) / ((m ^ 2 : ℕ) : ℚ) : ℚ) : WithTop ℚ) := WithTop.coe_sum _ _
    _ ≤ ∑ b, v b := Finset.sum_le_sum fun b _ => hpt b

end GlobalTheory.EtaVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValForm

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem hasVal_coord {D : DegPre V} {χ : D.X} {n : ℤ} {r : V} (hn : QForm.QVal D ϖ χ n) (hr : PsiCoord D χ r) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨j, hj, h, e⟩ := hr
  have htop : LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j = ⊤ :=
    eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun _ => hj trivial)
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => -1) (D.psi χ) hn j htop h
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) (DegPre.toOpen (R := V) ⊤ r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
  have hid : (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r) = r := by
    simp only [DegPre.toOpen, RingHom.coe_comp, Function.comp_apply]
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    simp
  have hval : algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (DegPre.toOpen ⊤ r)) =
      c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    exact congrArg _ e
  rw [hid] at hval
  rw [hval]
  exact hasVal_mul_unit hc eV

omit [IsDiscreteValuationRing V] in
theorem hasVal_mul (hϖ : Irreducible ϖ) {a b : V} {n m : ℤ} (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    (hb : HasVal ϖ (algebraMap V (FractionRing V) b) m) :
    HasVal ϖ (algebraMap V (FractionRing V) (a * b)) (n + m) := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨u * v, ?_⟩
  rw [map_mul, hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero),
    Units.val_mul, map_mul]
  ring

omit [IsDiscreteValuationRing V] in
theorem logb_of_hasVal {a : V} {n : ℤ} (hn : 0 ≤ n) (ha : HasVal ϖ (algebraMap V (FractionRing V) a) n)
    {C : Type} [NormedField C] (f : V →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (p : ℝ) :
    Real.logb p ‖f a‖ = n * Real.logb p ‖f ϖ‖ := by
  obtain ⟨u, hu⟩ := ha
  lift n to ℕ using hn
  rw [zpow_natCast, ← map_pow, ← map_mul] at hu
  rw [IsFractionRing.injective V (FractionRing V) hu, map_mul, norm_mul, GlobalTheory.PeriodBalance.norm_unit f hf u,
    _root_.mul_one, map_pow, norm_pow, Real.logb_pow, Int.cast_natCast]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧ (∀ a b, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧ (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ ∀ (C : Type) [NormedField C] (f : V →+* C) (p : ℕ), Function.Injective f → (∀ a, ‖f a‖ ≤ 1) → ∀ a b, betaAt P.D.toPre f p a b = -Real.logb p ‖f ϖ‖ * (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b := by
  intro E _ _ _ H V _ _ _ _ _ G P ϖ hϖ cj hcj
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main V P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap V (FractionRing V) (hex χ).choose) (Q χ) := fun χ =>
    hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (hasVal_mul hϖ (hasVal_mul hϖ (hv (x • a + b)) (hv a)) (hv (H.bar x • b))) u
    have h2 := hasVal_mul hϖ (hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ :=
    LinearMap.mk₂ ℤ (fun a b => (QForm.bHom hϖ P.D hQ' a b : ℝ))
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply, Int.cast_add])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add (f := _), Int.cast_add])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, Int.cast_id])
  have hβ : ∀ a b, β a b = (QForm.bOf P.D.toPre Q a b : ℝ) := fun _ _ => rfl
  refine ⟨Q, ⟨β, fun a b => ?_, fun c c' hc a b => ?_⟩, hQ', h0, hβ, fun a => ?_, fun C _ f p _ hf a b => ?_⟩
  · rw [hβ, hβ, QForm.bOf_comm]
  · obtain rfl : c' = H.bar c := RingOfIntegers.ext (by rw [hc, hcj, H.bar_eq])
    rw [hβ, hβ, hbal]
  · show β a a = _
    rw [hβ, ← QForm.two_Q_eq hϖ P.D hQ']
    push_cast
    rfl
  · have hp : ∀ χ, vPsiAt P.D.toPre f p χ = -(Q χ * Real.logb p ‖f ϖ‖) := fun χ =>
      (dif_pos (hex χ)).trans (by rw [logb_of_hasVal (h0 χ) (hv χ) f hf])
    show _ = _ * β a b
    rw [hβ]
    simp only [betaAt, hp, QForm.bOf]
    push_cast
    ring

end GlobalTheory.ValForm
end
end
