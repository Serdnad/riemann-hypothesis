module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.ResComm

theorem comm_span {Λ M C : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] [AddCommGroup C] (S : Set (Module.End Λ M))
    (φ : M →+ C) (h : ∀ A ∈ S, ∀ B ∈ S, ∀ m, φ (A (B m)) = φ (B (A m))) :
    ∀ A ∈ Submodule.span Λ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by

  have key : ∀ A ∈ S, ∀ B ∈ Submodule.span Λ S, ∀ m, φ (A (B m)) = φ (B (A m)) := by
    intro A hA B hB
    induction hB using Submodule.span_induction with
    | mem B hB => exact h A hA B hB
    | zero => intro m; simp
    | add B₁ B₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
    | smul c B _ hB' =>
      intro m
      simp only [LinearMap.smul_apply, ← map_smul]
      exact hB' (c • m)
  intro A hA B hB
  induction hA using Submodule.span_induction with
  | mem A hA => exact key A hA B hB
  | zero => intro m; simp
  | add A₁ A₂ _ _ h₁ h₂ => intro m; simp [h₁, h₂]
  | smul c A _ hA' =>
    intro m
    simp only [LinearMap.smul_apply, ← map_smul]
    exact hA' (c • m)

theorem act_add {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (P Q : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((P + Q).map (algebraMap O Λ)) =
      matAct (P.map (algebraMap O Λ)) + matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem act_smul {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (c : O) (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) ((c • P).map (algebraMap O Λ)) = algebraMap O Λ c • matAct (P.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [matAct, mul_smul, Finset.smul_sum]

theorem act_congr {O Λ K : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ]
    [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) (P Q : Matrix (Fin r) (Fin r) O)
    (h : P.map (IsLocalRing.residue O) = Q.map (IsLocalRing.residue O)) :
    matAct (M := K) (P.map (algebraMap O Λ)) = matAct (Q.map (algebraMap O Λ)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_

  have hPQ : P i j - Q i j ∈ IsLocalRing.maximalIdeal O := by
    have e := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at e
    exact Ideal.Quotient.eq.mp e
  have hΛ : algebraMap O Λ (P i j - Q i j) ∈ IsLocalRing.maximalIdeal Λ :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hPQ) (isUnit_of_map_unit (algebraMap O Λ) _ hu))
  have e := hm _ hΛ (v j)
  rwa [map_sub, sub_smul, sub_eq_zero] at e

private theorem matAct_single {O Λ K : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K] [Module Λ K] {r : ℕ}
    (a b : Fin r) (v : Fin r → K) :
    matAct (M := K) ((Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0).map (algebraMap O Λ)) v =
      Pi.single a (v b) := by
  funext i
  simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.of_apply]
  by_cases hi : i = a
  · subst hi
    simp [apply_ite (algebraMap O Λ), ite_smul]
  · simp [hi]

private theorem matAct_of_span_residue_spans {Γ O Λ K : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (hm : ∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0)
    (hsp : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (P : Matrix (Fin r) (Fin r) O) :
    matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) := by

  have lift : ∀ X : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O),
      ∃ P' : Matrix (Fin r) (Fin r) O, P'.map (IsLocalRing.residue O) = X := fun X =>
    ⟨X.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq IsLocalRing.residue_surjective]⟩

  suffices H : ∀ X ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g =>
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)),
      ∀ P : Matrix (Fin r) (Fin r) O, P.map (IsLocalRing.residue O) = X →
        matAct (M := K) (P.map (algebraMap O Λ)) ∈ Submodule.span Λ (Set.range fun g =>
          matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ))) by
    exact H _ (by rw [hsp]; exact Submodule.mem_top) P rfl
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨g, rfl⟩ := hX
    intro P hP
    rw [act_congr (K := K) hm P _ hP]
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    intro P hP
    have hP0 : P.map (IsLocalRing.residue O) = (0 : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O) := by
      rw [hP]; ext i j; simp
    rw [act_congr (K := K) hm P 0 hP0]
    have h0 : matAct (M := K) ((0 : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) = 0 := by
      refine LinearMap.ext fun v => funext fun i => ?_
      simp [matAct]
    rw [h0]
    exact Submodule.zero_mem _
  | add X Y _ _ hX hY =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    have hP₂ : (P - P₁).map (IsLocalRing.residue O) = Y := by
      have e : (P - P₁).map (IsLocalRing.residue O) =
          P.map (IsLocalRing.residue O) - P₁.map (IsLocalRing.residue O) := by
        ext i j; simp
      rw [e, hP, hP₁, add_sub_cancel_left]
    have e : P = P₁ + (P - P₁) := by abel
    rw [e, act_add]
    exact Submodule.add_mem _ (hX P₁ hP₁) (hY _ hP₂)
  | smul c X _ hX =>
    intro P hP
    obtain ⟨P₁, hP₁⟩ := lift X
    obtain ⟨c₀, rfl⟩ := IsLocalRing.residue_surjective c
    have h' : P.map (IsLocalRing.residue O) = (c₀ • P₁).map (IsLocalRing.residue O) := by
      rw [hP, ← hP₁]; ext i j; simp
    rw [act_congr (K := K) hm P _ h', act_smul]
    exact Submodule.smul_mem _ _ (hX P₁ hP₁)

private theorem matAct_rep {Γ O Λ K : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] [AddCommGroup K]
    [Module Λ K] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn (twGL ρ χ) κ K g m = ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) •
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)) m := by
  have e : (((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) =
      (((χ g)⁻¹ : Oˣ) : O) • ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) := by
    simp [twGL, scalGL, Matrix.smul_eq_diagonal_mul]
  show ((κ g : Λ) • matAct (M := K) ((((twGL ρ χ) g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map
    (algebraMap O Λ))) m = _
  rw [e, act_smul, smul_smul]
  rfl

theorem eq_zero_of_comm : ∀ (Γ O Λ K C : Type) [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ] [Algebra O Λ] [IsLocalHom (algebraMap O Λ)] [AddCommGroup K] [Module Λ K] [AddCommGroup C] (r : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ) (κ : Γ →* Λˣ), 2 ≤ r → (∀ x ∈ IsLocalRing.maximalIdeal Λ, ∀ k : K, x • k = 0) → Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → ∀ φ : (Fin r → K) →+ C, (∀ g h m, φ (repOn (twGL ρ χ) κ K g (repOn (twGL ρ χ) κ K h m)) = φ (repOn (twGL ρ χ) κ K h (repOn (twGL ρ χ) κ K g m))) → φ = 0 := by
  intro Γ O Λ K C _ _ _ _ _ _ _ _ _ _ r ρ χ κ hr hm hsp φ hφ

  have hunit : ∀ g, IsUnit ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) := fun g =>
    (κ g).isUnit.mul (((χ g)⁻¹).isUnit.map _)
  have hcomm : ∀ A ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ B ∈ Set.range fun g =>
      matAct (M := K) (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O Λ)),
      ∀ m, φ (A (B m)) = φ (B (A m)) := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ m
    obtain ⟨w, hw⟩ : ∃ w : Λ, ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) * w = 1 :=
      ⟨(((hunit g).mul (hunit h)).unit⁻¹ : Λˣ), by simp⟩
    have e := hφ g h (w • m)
    simp only [matAct_rep, map_smul, smul_smul] at e
    have e1 : w * ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) *
        ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    have e2 : w * ((κ g : Λ) * algebraMap O Λ (((χ g)⁻¹ : Oˣ) : O)) *
        ((κ h : Λ) * algebraMap O Λ (((χ h)⁻¹ : Oˣ) : O)) = 1 := by linear_combination hw
    rw [e1, e2, one_smul, one_smul] at e
    exact e

  have hall : ∀ (P Q : Matrix (Fin r) (Fin r) O) (m : Fin r → K),
      φ (matAct (M := K) (P.map (algebraMap O Λ)) (matAct (M := K) (Q.map (algebraMap O Λ)) m)) =
        φ (matAct (M := K) (Q.map (algebraMap O Λ)) (matAct (M := K) (P.map (algebraMap O Λ)) m)) :=
    fun P Q => comm_span _ φ hcomm _ (matAct_of_span_residue_spans ρ hm hsp P) _ (matAct_of_span_residue_spans ρ hm hsp Q)

  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have hsingle : ∀ (a : Fin r) (x : K), φ (Pi.single a x) = 0 := by
    intro a x
    obtain ⟨b, hb⟩ := exists_ne a
    have e := hall (Matrix.of fun i j => if i = a ∧ j = b then (1 : O) else 0)
      (Matrix.of fun i j => if i = b ∧ j = b then (1 : O) else 0) (Pi.single b x)
    simp only [matAct_single] at e
    simpa [Pi.single_eq_of_ne hb] using e
  refine AddMonoidHom.ext fun m => ?_

  rw [← Finset.univ_sum_single m, map_sum]
  simp [hsingle]

end GlobalTheory.ResComm
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NoJumpMult

open Module TensorProduct

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  have h := PD.Fil_anti a
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  have : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
          (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from h))) := by
    ext x y; rfl
  rw [this]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a ≤ Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (hpos : 0 < finrank LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ))
    (hj : Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : Formalism.WeaklyAdmissibleFiltrations.multV PD ρ τ a ≠ 0 := by
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)
  have hlt : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) < Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) hj
  have := Submodule.finrank_lt_finrank_of_lt hlt
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega
end Gen

end GlobalTheory.NoJumpMult

namespace GlobalTheory.NoJumpMult

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  unfold Formalism.BasicNotions.Ranks.r; omega

theorem noJump_of_jumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D bkP i s ι J hH hJ hG v hv τ a ha
    obtain ⟨τc, hτc, -⟩ := GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
    have hdR := (hH v hv (Tgl i s) (Set.mem_insert_of_mem _ rfl)).1
    have hK : 0 < Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 := by
      have := (bkP.br i v hv).Kw.2
      exact Module.finrank_pos
    have hpos : 0 < Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) := by
      have : Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) =
          Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 * D.R.r := hdR
      rw [this]; exact Nat.mul_pos hK (r_pos D)
    have hm := multV_ne_zero _ _ τ a hpos ha
    rw [hJ v hv τ τc hτc a] at hm
    have hmem : a ∈ J τc := by
      by_contra hn
      exact hm (by simp [Multiset.count_eq_zero.mpr hn])
    exact (hG τc).2.2 a hmem

end GlobalTheory.NoJumpMult
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.arith {α : Type} [Fintype α] [DecidableEq α] (f : α → ℤ) (h0 : ∑ z, f z = 0) (hf : f ≠ 0) :
    ∃ x y, x ≠ y ∧ ∑ z, (f z + eps x y z) = 0 ∧ ∑ z, (f z + eps x y z) ^ 2 < ∑ z, f z ^ 2 := by
  have hx : ∃ x, 0 < f x := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  have hy : ∃ y, f y < 0 := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x ≠ y := fun e => by rw [e] at hx; omega
  have e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x := by
    intro g
    have : ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0) := by
      intro z
      unfold eps
      by_cases a : z = x
      · subst a; simp [hxy]
      · by_cases b : z = y
        · subst b; simp [a]
        · simp [a, b]
    simp [this, Finset.sum_sub_distrib]
  have ex : eps x y x = -1 := by simp [eps]
  have ey : eps x y y = 1 := by simp [eps, hxy.symm]
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have := e1 fun _ => 1
    simp only [one_mul] at this
    rw [Finset.sum_add_distrib, h0, this]; simp
  · have a := e1 f
    have b := e1 (eps x y)
    have : ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, a, b, ex, ey]
    omega

theorem GlobalTheory.PMon.matThm_of_steps : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  intro hF hT hS hR hM l _ P AI T
  suffices H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N →
      ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from
    fun n _ _ K r ρ => H _ n rfl K r ρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro n _ _ hn K r ρ hρ hd
  obtain ⟨w, hw⟩ := (hF l P AI T n K r ρ hρ).1 hd
  obtain ⟨K', r', ρ', w', h1, h2, h3, h4⟩ := hT l P AI T n K r ρ w hρ hw
  apply h4
  suffices G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v →
      ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from
    G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl
  intro S
  induction S using Nat.strong_induction_on with
  | _ S IS =>
  intro σ v a1 a2 a3 a4
  by_cases hv : (fun z : Fin r' × n => v z.1 z.2) = 0
  · have : v = 0 := funext fun m => funext fun j => congrFun hv (m, j)
    subst this
    exact hS l P AI T n K' r' σ a1 a2
  by_cases hs : Splits r' σ
  · exact hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs
      fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2
  obtain ⟨x, y, hxy, c1, c2⟩ := GlobalTheory.PMon.arith _ a3 hv
  obtain ⟨τ, b1, b2, b3⟩ := hM l P AI T n K' r' σ v x y hxy a1 a2 hs
  refine b3 (IS _ ?_ τ _ b1 b2 c1 rfl)
  have p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S
  omega
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_stableLattice_integralCharacter : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  first | exact @GlobalTheory.CharLat.exists_equiv_charLattice | exact GlobalTheory.CharLat.exists_equiv_charLattice | (intros; apply GlobalTheory.CharLat.exists_equiv_charLattice <;> assumption)
end
