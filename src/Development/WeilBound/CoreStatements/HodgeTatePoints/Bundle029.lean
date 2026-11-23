module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle007
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle026
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FrameExpandLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle021
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.CategoryTheory.Category.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle054
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Lemma
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
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle020
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.DualLattices.PowMemCarrier
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem chart_comp_zero : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y :=
  chart_comp_zero_of @PositivityTheory.HtPt.Gc.test_div @PositivityTheory.HtPt.Gc.test_descend @PositivityTheory.HtPt.Gb.red_omHT_bc

end PositivityTheory.HtPt.Gd
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem chartMon_ne_zero {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem trivflag_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [CharZero Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R m j k : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R (j + k) V) (σ : E →+* Ω) (d : Ω) (dd : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, chartRing o (mseg y) s.1) (i : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)) →ₗ[chartRing o (mseg y) s.1] (Fin (j + k) → chartRing o (mseg y) s.1)) (bW : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin j) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)))) (bM : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin k) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) (wW : Fin j → Module.Dual Ω V) (wM : Fin k → V) (b : Fin (j + k) → K → ℤ), (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, IsFractionRing (chartRing o (mseg y) s.1) Ω) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1) → (∀ s, (dd s : Ω) = d ∧ GeneratesDiff σ (dd s)) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ') → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ m) • z) → (∀ s, (Dc s).IsDualMap σ (dd s) m (i s) ∧ (Dc s).ExactMod σ m (i s) ∧ ∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) → m ≤ R → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin j → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.castAdd k a)) ∧ ∀ z : (Dc s).omHT (σ.comp c.toRingHom), ((bW s a z : chartRing o (mseg y) s.1) : Ω) = ∑ a', cf a' * wW a' z) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin k → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.natAdd j a)) ∧ ((bM s a : (Dc s).omHT σ) : V) = ∑ a', cf a' • wM a') → Num.TrivFlagMod o ((p : o) ^ m) y (j + k) b := by
  intro o _ Ω _ _ K _ J _ y _ E _ _ c hc p R m j k _ V _ _ Dc σ d dd i bW bM wW wM b hfr hint hdd hρe hM hh hi hm
    hW hMb
  classical
  have hfe := fun s => frame_exists _ Ω Subtype.val_injective E c hc p R (j + k) V (Dc s) σ m j k (i s) (bW s) (bM s)
    finSumFinEquiv (hi s).2.2 (hi s).2.1
  choose g hg using fun s => (hfe s).1
  choose cf cf1 cf2 cf3 using hW
  have hϖ : algebraMap o Ω ((p : o) ^ m) = (p : Ω) ^ m := by simp
  refine ⟨fun s => if h : mseg y s ≠ 0 then
    ((g ⟨s, h⟩).map (fun a => (a : Ω))).submatrix id finSumFinEquiv.symm else 0, fun s hs => ?_,
    fun s t hs ht => ?_⟩
  · simp only [dif_pos hs]
    refine ⟨fun a a' => (g ⟨s, hs⟩ _ _).2, ?_⟩
    obtain ⟨h, r, e⟩ := (hfe ⟨s, hs⟩).2 _ (hg ⟨s, hs⟩)
    refine ⟨h, h.2, r, r.2, ?_⟩
    have := congrArg (chartRing o (mseg y) s).val e
    rw [map_mul, AlgHom.map_det] at this
    rw [hϖ, Matrix.submatrix_map]
    simpa using this
  · simp only [dif_pos hs, dif_pos ht, hϖ]
    haveI := hfr ⟨t, ht⟩
    have hu := div_mem_chartRing (o := o) (mseg y) t s
    have hu0 : mseg y s / mseg y t ≠ 0 := div_ne_zero hs ht
    have hAL : ∀ a ∈ chartRing o (mseg y) s, a ∈ loc _ _ hu := fun a ha =>
      exists_pow_mul_mem_chartRing (mseg y) s t hs ha
    obtain ⟨T, T1, T2, T3⟩ := tri wW (fun a => ∑ a', cf ⟨s, hs⟩ a a' • wW a') (fun a => ∑ a', cf ⟨t, ht⟩ a a' • wW a')
      (fun a => chartMon y s (b (Fin.castAdd k a))) (fun a => chartMon y t (b (Fin.castAdd k a)))
      (fun a => chartMon_ne_zero ht _) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩)
    obtain ⟨S, S1, S2, S3⟩ := tri wM (fun a => (bM ⟨s, hs⟩ a : V)) (fun a => (bM ⟨t, ht⟩ a : V))
      (fun a => chartMon y s (b (Fin.natAdd j a))) (fun a => chartMon y t (b (Fin.natAdd j a)))
      (fun a => chartMon_ne_zero ht _) (hMb ⟨s, hs⟩) (hMb ⟨t, ht⟩)
    obtain ⟨X, Z, hU, hZ, e⟩ := overlap (hu := hu) hc hu0 hAL (Dc ⟨s, hs⟩) (Dc ⟨t, ht⟩) hm (hint ⟨t, ht⟩ σ)
      (dd ⟨s, hs⟩) (dd ⟨t, ht⟩) ((hdd _).1.trans (hdd _).1.symm) (hdd _).2 (hρe _ _).1 (hρe _ _).2
      (hM ⟨s, hs⟩ ⟨t, ht⟩ σ) (by rw [inv_div]; exact hM ⟨t, ht⟩ ⟨s, hs⟩ _) (hh ⟨s, hs⟩ ⟨t, ht⟩)
      (hi _).1 (hi _).1 (hi _).2.1 (hg _) (hg _) _ _
      (fun a z => by rw [cf3]; simp) (fun a z => by rw [cf3]; simp) T T3 S S3
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := (((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hU a a')).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hZ a a'))).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hAL _ (g ⟨s, hs⟩ a a').2))).exists
    refine ⟨n, (mseg y s / mseg y t) ^ n •
      (Matrix.fromBlocks T X 0 S).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      (mseg y s / mseg y t) ^ n • Z.submatrix id finSumFinEquiv.symm, fun a a' => h1 _ _, fun a a' => h2 _ _,
      fun a a' h => ?_, fun a => ?_, fun a a' => h3 _ _, ?_⟩
    · rw [Matrix.smul_apply, Matrix.submatrix_apply]
      refine smul_eq_zero_of_right _ ?_
      induction a using Fin.addCases with
      | left a =>
        induction a' using Fin.addCases with
        | left a' => simpa using T1 a a' h
        | right a' =>
          have : j + (a' : ℕ) < a := h
          omega
      | right a =>
        induction a' using Fin.addCases with
        | left a' => simp
        | right a' => simpa using S1 a a' (by simpa using h)
    · rw [Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
      congr 1
      induction a using Fin.addCases with
      | left a => simpa using T2 a
      | right a => simpa using S2 a
    · rw [Matrix.mul_smul, smul_comm, ← smul_add, Matrix.submatrix_mul_equiv, e]
      rfl

end PositivityTheory.HtPt.Ge
end

section

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
  [Fintype F] [DecidableEq F]
variable {N X : Type} [AddCommGroup N] [Module F N] [AddCommGroup X] [Module F X]

def projL (χ : MulChar F R) : (N → C) →ₗ[R] (N → C) where
  toFun := GlobalTheory.CompanionTheory.Ar.GR.proj χ
  map_add' g h := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r g := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

lemma projL_apply (χ : MulChar F R) (g : N → C) (x : N) :
    projL χ g x = (Fintype.card Fˣ : C)⁻¹ *
      ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) := rfl

lemma exists_inv_card {v : Valuation C NNReal} (hv : v.Integers R) (p : ℕ) [Fact p.Prime]
    (hvp : v (p : C) < 1) [CharP F p] :
    ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹ := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : v ((Fintype.card F : ℕ) : C) < 1 := by
    rw [hn, Nat.cast_pow, map_pow]
    exact pow_lt_one₀ zero_le hvp n.ne_zero
  have h1 : v (Fintype.card Fˣ : C) = 1 := by
    rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one, Valuation.map_sub_swap]
    exact v.map_one_sub_of_lt hq
  exact hv.exists_of_le_one (by rw [map_inv₀, h1, inv_one])

lemma projL_mem (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    (S : Submodule R (N → C)) (hS : FStable (F := F) S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
    funext x
    rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
  rw [this]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))

omit [Fintype F] [DecidableEq F] in
lemma fstable_sq {M : Submodule R (N → C)} (hM : FStable (F := F) M) :
    FStable (F := F) (sqIdeal (augIdeal M)) :=
  fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom M M (hM a) hg

omit [Fintype F] [DecidableEq F] in
lemma mul_inv_unit (χ : MulChar F R) (a : Fˣ) : χ (a : F) * χ⁻¹ (a : F) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

omit [Fintype F] [DecidableEq F] in
lemma eig_le_aug (M : Submodule R (N → C)) (χ : MulChar F R) : eig M χ ≤ augIdeal M := by
  intro g hg
  rw [mem_aug]
  refine ⟨hg.1, ?_⟩
  have := hg.2 0 0
  rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at this

lemma projL_eig (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    {M : Submodule R (N → C)} (hM : FStable (F := F) M) {g : N → C} (hg : g ∈ augIdeal M) :
    projL χ g ∈ eig M χ := by
  rw [mem_aug] at hg
  refine ⟨projL_mem hu χ M hM hg.1, fun a x => ?_⟩
  by_cases ha : a = 0
  · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
    simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
  · obtain ⟨a, rfl⟩ := (isUnit_iff_ne_zero.2 ha)
    rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
      ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
        (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
      mul_left_comm, mul_inv_unit, mul_one]

lemma projL_self [CharZero C] (χ : MulChar F R) {M : Submodule R (N → C)} {g : N → C}
    (hg : g ∈ eig M χ) : projL χ g = g := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) = g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, mul_comm (χ⁻¹ _), mul_inv_unit, map_one, one_mul]
  rw [projL_apply]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_ne [IsDomain R] {χ χ' : MulChar F R} (hne : χ ≠ χ') {M : Submodule R (N → C)}
    {g : N → C} (hg : g ∈ eig M χ') : projL χ g = 0 := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) =
      algebraMap R C ((χ⁻¹ * χ') (a : F)) * g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, MulChar.mul_apply]
  have h0 : ∑ a : Fˣ, (χ⁻¹ * χ') (a : F) = 0 := by
    refine sum_hom_units_eq_zero ((χ⁻¹ * χ').toMonoidHom.comp (Units.coeHom F)) fun h1 => hne ?_
    rw [← inv_mul_eq_one]
    refine MulChar.ext fun a => ?_
    rw [MulChar.one_apply_coe]
    exact DFunLike.congr_fun h1 a
  rw [projL_apply]
  simp only [h]

  rw [← Finset.sum_mul, ← map_sum, h0, map_zero, zero_mul, mul_zero, Pi.zero_apply]

lemma sum_projL [CharZero C] [IsDomain R] (σ : MulChar F R)
    (hσ : ∀ a : Fˣ, σ (a : F) = 1 → a = 1) (g : N → C) :
    ∑ i : Fin (Fintype.card Fˣ), projL (σ ^ ((i : ℕ) + 1)) g = g := by
  funext x
  have h : ∀ a : Fˣ, ∑ i : Fin (Fintype.card Fˣ), (σ ^ ((i : ℕ) + 1))⁻¹ (a : F) =
      if a = 1 then (Fintype.card Fˣ : R) else 0 := by
    intro a
    split_ifs with ha
    · simp [ha]
    · have hp : ∀ i : ℕ, (σ ^ (i + 1))⁻¹ (a : F) = σ⁻¹ (a : F) ^ i * σ⁻¹ (a : F) := fun i => by
        rw [← inv_pow, MulChar.pow_apply_coe, pow_succ]
      simp only [hp]
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => σ⁻¹ (a : F) ^ i)]
      have h1 := geom_sum_mul (σ⁻¹ (a : F)) (Fintype.card Fˣ)
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one,
        sub_self] at h1
      have h2 : σ⁻¹ (a : F) - 1 ≠ 0 := fun h => ha (hσ a (by
        have := mul_inv_unit σ a
        rwa [sub_eq_zero.1 h, mul_one] at this))
      rw [(mul_eq_zero.1 h1).resolve_right h2, zero_mul]
  rw [Finset.sum_apply]
  simp only [projL_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]

  simp only [← Finset.sum_mul, ← map_sum, h]
  rw [Finset.sum_eq_single 1 (fun a _ ha => by simp [ha]) (by simp)]
  rw [if_pos rfl, map_natCast, Units.val_one, one_smul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_funLeft (χ : MulChar F R) (φ : X →ₗ[F] N) (g : N → C) :
    projL χ (LinearMap.funLeft R C φ g) = LinearMap.funLeft R C φ (projL χ g) := by
  funext x
  simp only [projL_apply, LinearMap.funLeft_apply, map_smul]

omit [Fintype F] [DecidableEq F] in
lemma eig_pull (χ : MulChar F R) (φ : X →ₗ[F] N) (M : Submodule R (N → C))
    (M' : Submodule R (X → C)) (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C}
    (hg : g ∈ eig M χ) : LinearMap.funLeft R C φ g ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simp only [LinearMap.funLeft_apply, map_smul, hg.2]⟩

end Gen

end PositivityTheory.HtPt.Rc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartDer

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have hv' : LieEx.zsec y ≫ (v : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G v).1 hv
  have hw' : LieEx.zsec y ≫ (w : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G w).1 hw
  have z : ∀ t : LieEx.ob y C ⟶ G, LieEx.zsec y ≫ t = 1 → LieEx.hom y (0 : C →ₗ[C] C) ≫ t = 1 := fun t ht => by
    rw [LieEx.hom_zero, Category.assoc, ht, MonObj.comp_one]
  obtain ⟨t, ht⟩ : ∃ t : LieEx.ob y (C × C) ⟶ G, t = (LieEx.hom y (LinearMap.inl C C C) ≫ (v : LieEx.ob y C ⟶ G)) *
    (LieEx.hom y (LinearMap.inr C C C) ≫ (w : LieEx.ob y C ⟶ G)) := ⟨_, rfl⟩
  have hz : LieEx.zsec y ≫ t = 1 := by
    rw [ht, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv', hw',
      _root_.mul_one]
  have h1 : LieEx.hom y (LinearMap.fst C C C) ≫ t = v := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z w hw', _root_.mul_one]
  have h2 : LieEx.hom y (LinearMap.snd C C C) ≫ t = w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv', _root_.one_mul]
  have h3 : LieEx.hom y (LinearMap.fst C C C + LinearMap.snd C C C) ≫ t = v * w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      add_zero, zero_add, LieEx.hom_id, Category.id_comp]
  have hzl : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) ≫ t.left =
      spMap u ≫ hU.fromSpec := (congrArg CommaMorphism.left hz).trans hu
  have hle : ⊤ ≤ t.left ⁻¹ᵁ U := by
    intro p _
    obtain ⟨q, rfl⟩ := LieVB.surj_fst (T := C) (M := C × C) p
    have e : t.left (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) q) =
        hU.fromSpec (spMap u q) := congrArg (fun f : Sp C ⟶ G.left => f q) hzl
    show t.left _ ∈ U
    rw [e]
    exact hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ(G.left, U) →+* TrivSqZeroExt C (C × C), spMap Φ ≫ hU.fromSpec = t.left :=
    ⟨_, TanMul.ringOf_spec (A := TrivSqZeroExt C (C × C)) hU t.left hle⟩
  have key : ∀ (l : C × C →ₗ[C] C), (LieEx.hom y l ≫ t).left =
      spMap ((TrivSqZeroExt.map l).toRingHom.comp Φ) ≫ hU.fromSpec := fun l => by
    rw [spMap_comp, Category.assoc, hΦ]
    rfl
  have e1 := TanMul.ring_inj hU (ev.symm.trans ((congrArg CommaMorphism.left h1).symm.trans (key _)))
  have e2 := TanMul.ring_inj hU (ew.symm.trans ((congrArg CommaMorphism.left h2).symm.trans (key _)))
  have e3 : χ = (TrivSqZeroExt.map (LinearMap.fst C C C + LinearMap.snd C C C)).toRingHom.comp Φ := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [hχ, ← hφ, e1]
      simp
    · rw [hs, e1, e2]
      simp
  rw [e3]
  exact (congrArg CommaMorphism.left h3).symm.trans (key _)

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  apply GlobalTheory.CompanionTheory.Ar.ChartDer.lieChart_of_smooth_chart <;> assumption

end PositivityTheory.HtPt.Htat.Lie
end
end
