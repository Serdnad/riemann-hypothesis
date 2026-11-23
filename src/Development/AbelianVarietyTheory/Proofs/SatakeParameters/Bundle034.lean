module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle028
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle029
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004

@[expose] public section

section

open Matrix

theorem _root_.GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) → ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | exact GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker <;> assumption)
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut

noncomputable section

namespace GlobalTheory.SumTransIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem sumRt_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsSubrep ρ S) (hiso : Formalism.L2.NG.IsoRep S S')
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (f' : Formalism.AUTREP.GAf L n → W) (hf' : f' ∈ S')
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f' = f') :
    ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' = c • f' := by
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : Formalism.AUTREP.GAf L n,
      ((T ⟨Formalism.L2.NG.rt L n h f, hS.stable h _ f.2⟩ : S') : Formalism.AUTREP.GAf L n → W) = Formalism.L2.NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ (f : Formalism.AUTREP.GAf L n → W) = f := by
    intro κ hκ ht
    have h1 := hrt κ
    rw [hfix κ hκ ht] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨Formalism.L2.NG.rt L n (r γ) f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f := by
    simp only [σ, Submodule.coe_sum]
  have hTσ : ((T σ : S') : Formalism.AUTREP.GAf L n → W) = ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f' := by

    simp only [σ, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt _
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : Formalism.AUTREP.GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem iSup_finset_stable (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W)))
    (ht : ∀ i ∈ t, ∀ h, ∀ f ∈ i, Formalism.L2.NG.rt L n h f ∈ i) (h : Formalism.AUTREP.GAf L n) :
    ∀ f ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h f ∈ (⨆ i ∈ t, i) := by
  have hle : (⨆ i ∈ t, i) ≤ (⨆ i ∈ t, i).comap (Formalism.L2.NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ t) => i) i hi) (ht i hi h f hf)
  exact fun f hf => hle hf

theorem sumRt_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (Formalism.AUTREP.GAf L n → W)}
    (hS : Formalism.L2.NG.IsIrrRep ρ S)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {ι : Type} (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f)
    (t : Finset (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) :
    ((↑t : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → W))) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : Formalism.L2.NG.IsIrrRep ρ a ∧ Formalism.L2.NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | Formalism.L2.NG.IsIrrRep ρ S' ∧ Formalism.L2.NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), Formalism.L2.NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      iSup_finset_stable t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : Formalism.L2.NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : Formalism.L2.NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : Formalism.L2.NG.rt L n κ y - y = z - Formalism.L2.NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      have e1 := sumRt_iso hS.1 haF.2 v R r c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

theorem sumRt_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n)
    (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S →
    ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ),
    (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) →
    ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) →
      ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS v ι R r c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact sumRt_finset_sum hS v R r c hc t ht f hft hfix

end GlobalTheory.SumTransIso
end
end

section

noncomputable section

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} (P : Matrix (Fin a) (Fin b) L) (Q : Matrix (Fin b) (Fin c) L)
    (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) (hQ : ∀ i j, Q i j ∈ Formalism.UG.intL L) :
    ∀ i j, (P * Q) i j ∈ Formalism.UG.intL L := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hQ k j)

theorem trace_int {a : ℕ} (P : Matrix (Fin a) (Fin a) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    P.trace ∈ Formalism.UG.intL L :=
  Subring.sum_mem _ fun i _ => hP i i

theorem conjT_int {a b : ℕ} (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (P : Matrix (Fin a) (Fin b) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (P.map σ)) i j ∈ Formalism.UG.intL L := by
  intro i j
  show Valued.v (σ (P j i)) ≤ 1
  rw [hσ]; exact hP j i

theorem phase_shift (σ : L →+* L) (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h2 : Valued.v (2 : L) = 1) (ψ : AddChar L ℂ) (hψ : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (u u' : L) (hd : u - u' ∈ Formalism.UG.intL L) (h : ψ ((u + σ u) / 2) = 1) :
    ψ ((u' + σ u') / 2) = 1 := by
  have he : ((u - u') + σ (u - u')) / 2 ∈ Formalism.UG.intL L := by
    show Valued.v (((u - u') + σ (u - u')) / 2) ≤ 1
    rw [map_div₀, h2, div_one]
    refine (Formalism.UG.intL L).add_mem hd ?_
    show Valued.v (σ (u - u')) ≤ 1
    rw [hσ]; exact hd
  have hs : σ (((u - u') + σ (u - u')) / 2) = ((u - u') + σ (u - u')) / 2 := by
    rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have heq : (u' + σ u') / 2 = (u + σ u) / 2 - ((u - u') + σ (u - u')) / 2 := by
    rw [map_sub]; ring
  rw [heq, AddChar.map_sub_eq_div, h, hψ _ he hs, div_one]

end GlobalTheory.Hk3.ShiftPhase

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

theorem conjT_mul_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ} (σ : L →+* L)
    (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (C : Matrix (Fin a) (Fin a) L) (hC : ∀ i j, σ (C i j) = - C j i)
    (x : Matrix (Fin a) (Fin b) L) (hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (x.map σ) * C) i j ∈ Formalism.UG.intL L := by
  intro j k
  have h : (Matrix.transpose (x.map σ) * C) j k = - σ ((C * x) k j) := by

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hC,
    ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  refine (Formalism.UG.intL L).neg_mem ?_
  show Valued.v (σ _) ≤ 1
  rw [hσ]; exact hCx k j

theorem shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  intro L _ _ ϖ σ q δ n n' A ψ hU hq hA hδ _ hψ x l hl hx C hC hCv hCxl
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, -⟩ := hU
  have hCi : ∀ i j, C i j ∈ Formalism.UG.intL L := fun i j => (hCv i j).le
  have hCl : ∀ i j, (C * l) i j ∈ Formalism.UG.intL L := mul_int C l hCi hl
  have hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L := by
    have e : C * x = C * (x - l) + C * l := by rw [Matrix.mul_sub]; abel
    intro i j
    rw [e, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hCxl i j) (hCl i j)
  have hsub : Matrix.transpose ((x - l).map σ) = Matrix.transpose (x.map σ) - Matrix.transpose (l.map σ) := by
    ext i j; simp [map_sub]
  set X := Matrix.transpose (x.map σ) with hX
  set Y := Matrix.transpose (l.map σ) with hY
  have hYi : ∀ i j, Y i j ∈ Formalism.UG.intL L := conjT_int σ hσv l hl
  have hXC : ∀ i j, (X * C) i j ∈ Formalism.UG.intL L := conjT_mul_int σ hσσ hσv C hC x hCx
  have hd : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y)))
      = Matrix.trace (C * x * A * Y) + Matrix.trace (X * C * l * A) - Matrix.trace (C * l * A * Y) := by
    have h3 : Matrix.trace (C * (l * A * X)) = Matrix.trace (X * C * l * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    rw [h3]
    simp only [Matrix.mul_assoc]
    abel
  have hdi : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) ∈ Formalism.UG.intL L := by
    rw [hd]
    refine (Formalism.UG.intL L).sub_mem ((Formalism.UG.intL L).add_mem ?_ ?_) ?_
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCx hA) hYi)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hXC hl) hA)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCl hA) hYi)
  rw [hsub]
  refine phase_shift σ hσσ hσv h2 ψ hψ (δ * Matrix.trace (C * (x * A * X))) _ ?_ (hx C hC hCv hCx)
  rw [← mul_sub]
  refine (Formalism.UG.intL L).mul_mem ?_ hdi
  show Valued.v δ ≤ 1
  rw [hδ]

end GlobalTheory.Hk3.ShiftPhase
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_smithNormalForm_generators_exactOrders : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  first | exact @GlobalTheory.Hk3.snf_generators | exact GlobalTheory.Hk3.snf_generators | (intros; apply GlobalTheory.Hk3.snf_generators <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem isIntegrallyClosed_sections_of_smooth_complex :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  intro Z _ s hsm U hU hg
  have hs : (s.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth s hsm ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  letI : Algebra Γ(Sp ℂ, ⊤) Γ(Z, U) := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
  let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  letI : Field Γ(Sp ℂ, ⊤) := (e.toMulEquiv.isField (Field.toIsField ℂ)).toField
  have : Nonempty U := ⟨⟨_, hg⟩⟩
  have : IsDomain Γ(Z, U) := inferInstance
  exact GlobalTheory.isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.qBinomial_sum_card_quotient_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : ℂ), ∑ j ∈ Finset.range (Module.finrank k V + 1), (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j = ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  first | exact @GlobalTheory.qBinomial_subspaces | exact GlobalTheory.qBinomial_subspaces | (intros; apply GlobalTheory.qBinomial_subspaces <;> assumption)
end
