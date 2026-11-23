module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle850
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle889
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle891
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CocLift

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem powerSeriesEvalTwoGroups_smul (c : MvPowerSeries (Fin d ⊕ Fin d) R) (r : R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (r • c) u v = r • at2 c u v :=
  subst_smul (hasSubst_elim u v hu hv) r c

theorem constantCoeff_powerSeriesEvalTwoGroups_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hc : constantCoeff c = 0) : constantCoeff (at2 c u v) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim u v hu hv) (fun s => by cases s <;> simp [hu, hv]) hc

theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim u v hu hv)]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_threeGroupsFirstVariables_eq_zero : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
theorem constantCoeff_threeGroupsSecondVariables_eq_zero : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
theorem constantCoeff_threeGroupsThirdVariables_eq_zero : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _

theorem cOp (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : ∀ i, constantCoeff (op μ u v i) = 0 :=
  fun i => constantCoeff_powerSeriesEvalTwoGroups_zero _ u v hu hv (hμ i)

theorem formalGroupLawCoboundaryTwo_smul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : cob2 μ (r • c) = r • cob2 μ c := by
  unfold cob2
  rw [powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, powerSeriesEvalTwoGroups_smul _ _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero]
  simp only [smul_sub, smul_add]

theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]
theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]
theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map h (op μ u v i)) = op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups h _ u v hu hv

theorem map_formalGroupLawCoboundaryTwo (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (cob2 μ c) = cob2 (fun i => map h (μ i)) (map h c) := by
  unfold cob2
  simp only [map_sub, map_add (f := _)]
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, mvPowerSeriesMap_evalTwoGroups h _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero,
    map_op h μ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero, map_op h μ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem cYX : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _
theorem cXX : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _

theorem swap_smul (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (r • c) = r • swap c :=
  powerSeriesEvalTwoGroups_smul c r _ _ cYX cXX

theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ cYX cXX]
  simp

end GlobalTheory.CocLift

namespace GlobalTheory.CocLift

theorem cocycle_lift : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (a : O), a ∣ p → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) O, constantCoeff c = 0 → (∀ α, a ∣ coeff α (cob2 μ c)) → (∀ α, a ∣ coeff α (swap c - c)) → ∃ g : MvPowerSeries (Fin d) C, QL μ ⊤ g ∧ lin g = 0 ∧ In (Ideal.span {a}) (cob1 (up C μ) g - map (algebraMap O C) c) := by
  intro p _ O C _ _ _ hF d μ hμ a ha c hc0 hcob hsw
  set A : C := algebraMap O C a with hA
  have hAu : IsUnit A := by
    obtain ⟨b, hb⟩ := ha
    have : (p : C) = A * algebraMap O C b := by rw [hA, ← map_mul, ← hb, map_natCast]
    exact isUnit_of_mul_isUnit_left (this ▸ hF.unit_p)
  obtain ⟨u, hu⟩ := hAu
  set ai : C := ↑u⁻¹ with hai
  have hAai : A * ai = 1 := by rw [hai, ← hu, Units.mul_inv]
  have hμc : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    simp [up, hμ.const i]
  set c' : MvPowerSeries (Fin d ⊕ Fin d) C := ai • map (algebraMap O C) c with hc'
  have hlift : IsLift (RingHom.id O) μ := by
    refine ⟨hμ.const, hμ.unit, hμ.comm, ?_⟩
    have : (fun i => map (RingHom.id O) (μ i)) = μ := by
      funext i; ext α; simp [coeff_map]
    rw [this]; exact hμ
  have hc'0 : constantCoeff c' = 0 := by
    simp [hc', hc0]
  have hden : ∀ α, ∃ k : ℕ, ∃ b ∈ (⊤ : Ideal O), (p : C) ^ k * coeff α c' = algebraMap O C b := by
    intro α
    obtain ⟨k, b, hb⟩ := hF.denom (coeff α c')
    exact ⟨k, b, Submodule.mem_top, hb⟩
  have hcob' : In (⊤ : Ideal O) (cob2 (up C μ) c') := by
    intro α
    obtain ⟨b, hb⟩ := hcob α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : cob2 (up C μ) c' = ai • map (algebraMap O C) (cob2 μ c) := by
      rw [hc', formalGroupLawCoboundaryTwo_smul _ hμc, map_formalGroupLawCoboundaryTwo _ _ hμ.const]; rfl
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  have hsw' : In (⊤ : Ideal O) (swap c' - c') := by
    intro α
    obtain ⟨b, hb⟩ := hsw α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : swap c' - c' = ai • map (algebraMap O C) (swap c - c) := by
      rw [hc', swap_smul, map_sub, map_swap, smul_sub]
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  obtain ⟨g', hg0, hglin, -, hgIn⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊤ ⊤ le_rfl c'
    (Or.inl hμ) hc'0 hden hcob' hsw'
  have hcob1 : cob1 (up C μ) (A • g') = A • cob1 (up C μ) g' := formalCoboundary_smul hμc A g'
  have hlin : lin (A • g') = 0 := by
    funext i
    have := congrFun hglin i
    simp only [lin, coeff_smul, Pi.zero_apply] at this ⊢
    rw [this, mul_zero]
  refine ⟨A • g', ⟨?_, ?_, ?_⟩, hlin, ?_⟩
  · simp [hg0]
  · intro i; exact ⟨0, Submodule.mem_top, by rw [hlin, map_zero]; rfl⟩
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨coeff α c - a * b, Submodule.mem_top, ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_sub, map_mul]
    linear_combination (algebraMap O C (coeff α c)) * hAai
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨a * (-b), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a), ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [map_sub, hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_mul, map_neg]
    linear_combination (algebraMap O C (coeff α c)) * hAai

end GlobalTheory.CocLift
end
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.LogLin

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {τ : Type}
    {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) =
      fun i => map h (op μ u v i) :=
  funext fun i => (mvPowerSeriesMap_evalTwoGroups h hu hv (μ i)).symm

theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]

theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]

theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

theorem map_assoc (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (ha : op μ (op μ x1 x2) x3 = op μ x1 (op μ x2 x3)) :
    op (fun i => map h (μ i)) (op (fun i => map h (μ i)) x1 x2) x3 =
      op (fun i => map h (μ i)) x1 (op (fun i => map h (μ i)) x2 x3) := by
  have h12 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  rw [← map_threeGroupsFirstVariables h, ← map_threeGroupsSecondVariables h, ← map_threeGroupsThirdVariables h, map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables CobCob.constantCoeff_threeGroupsSecondVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsSecondVariables CobCob.constantCoeff_threeGroupsThirdVariables, map_op h μ h12 CobCob.constantCoeff_threeGroupsThirdVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables h23, ha]

theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_formalGroupLawCoboundaryOne_eq (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map h (cob1 μ f) = cob1 (fun i => map h (μ i)) (map h f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hc),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (cob1 μ f) = 0 := by
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hc) hc hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf, sub_zero, sub_zero]

theorem lin_form (w : Fin d → R) (i : Fin d) :
    lin (∑ j, w j • (X j : MvPowerSeries (Fin d) R)) i = w i := by
  classical
  unfold lin
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.QLog.LogLin


open GlobalTheory.QLog.LogLin in
theorem GlobalTheory.QLog.exists_log_of_lin : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  intro p _ O C _ _ _ hF d μ hμ w
  classical
  let F : MvPowerSeries (Fin d) O := ∑ j, w j • (X j : MvPowerSeries (Fin d) O)
  have hF0 : constantCoeff F = 0 := by simp [F]
  let h : O →+* C := algebraMap O C
  have hup : up C μ = fun i => map h (μ i) := rfl
  have hc' : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    rw [hup]; simp only [constantCoeff_map, hμ.const i, map_zero]
  have hcmap : cob1 (up C μ) (map h F) = map h (cob1 μ F) :=
    (map_formalGroupLawCoboundaryOne_eq h μ hμ.const F).symm
  have hlift : IsLift (RingHom.id O) μ :=
    ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have rules := formalGroupLawCoboundaryTwo_coboundaryOne_alt C d (up C μ) hc' (map h F)
  have hass : op (up C μ) (op (up C μ) x1 x2) x3 = op (up C μ) x1 (op (up C μ) x2 x3) :=
    map_assoc h μ hμ.const hμ.assoc
  have hcomm : (fun i => swap (up C μ i)) = up C μ := by
    funext i; rw [hup]; dsimp only; rw [← map_swap, hμ.comm i]
  obtain ⟨g, hg0, hglin, -, hgc⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊥ ⊤ bot_le
    (cob1 (up C μ) (map h F)) (Or.inl hμ)
    (by rw [hcmap, constantCoeff_map, constantCoeff_formalGroupLawCoboundaryOne_eq_zero μ hμ.const hF0, map_zero])
    (fun α => ⟨0, coeff α (cob1 μ F), Submodule.mem_top, by
      rw [pow_zero, one_mul, hcmap, coeff_map]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.1, hass, sub_self, map_zero, map_zero]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.2.1, hcomm, sub_self, map_zero, map_zero]⟩)
  have hzero : cob1 (up C μ) (map h F) - cob1 (up C μ) g = 0 := by
    ext α
    obtain ⟨b, hb, he⟩ := hgc α
    rw [Ideal.mem_bot] at hb
    rw [he, hb, map_zero, map_zero]
  refine ⟨map h F - g, ?_, fun i => ?_, ?_⟩
  · rw [map_sub, constantCoeff_map, hF0, map_zero, hg0, sub_zero]
  · have := congrFun hglin i
    unfold lin at this ⊢
    rw [map_sub, coeff_map, this, Pi.zero_apply, sub_zero]
    exact congrArg h (lin_form w i)
  · rw [sub_eq_add_neg, formalCoboundary_add hc', ← neg_one_smul C g, formalCoboundary_smul hc', neg_one_smul,
      ← sub_eq_add_neg, hzero]
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k'), c.IsLawOf μ → c'.IsLawOf ν → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  first | exact @GlobalTheory.Katz.isHom_map_of_semiHom_ev | exact GlobalTheory.Katz.isHom_map_of_semiHom_ev | (intros; apply GlobalTheory.Katz.isHom_map_of_semiHom_ev <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.quasiPeriod_normalised_jet_modular_transform : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (κ : Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', HasLevel N L' ∧ L' = mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ wt (2 * s) κ * hfun (2 * s) (mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  first | exact @GlobalTheory.HilbFam.hfun_slash | exact GlobalTheory.HilbFam.hfun_slash | (intros; apply GlobalTheory.HilbFam.hfun_slash <;> assumption)
end

section

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma omegaFactor_ne_zero' {F : Type} [Field F] [NumberField F] (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 ≠ 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
  refine mul_ne_zero ?_ ?_
  · have h : (0:ℝ) < |((discr F : ℤ) : ℝ)| := by
      rw [abs_pos]; exact_mod_cast discr_ne_zero F
    positivity
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasSum_jet_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k * (a ξ * _root_.GlobalTheory.HilbFam.eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.HilbFam.lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t))) (_root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ c t) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ
  have h := (_root_.GlobalTheory.HilbFam.hasSum_iterD_gval_split F k 𝔞 𝔟 a₀ a x τ c t
    (_root_.GlobalTheory.HilbFam.word κ) hk ha hτ).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k)
  have hC : ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k ≠ 0 := by
    refine pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ?_) ?_)
    · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    · exact_mod_cast omegaFactor_ne_zero' 𝔞
  simp only [_root_.GlobalTheory.HilbFam.count_word_eq, mul_div_cancel₀ _ hC] at h
  exact h

end GlobalTheory.HilbFam
end
