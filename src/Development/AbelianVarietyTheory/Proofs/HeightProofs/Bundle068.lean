module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle096
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle282
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle223
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram


set_option autoImplicit false in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize Formalism.MainNotions.WeightAlgebra

theorem rows_of_pageFix : ∀ (eps : ℝ) (Fm : FamP eps), DC.PageFix Fm → 1000 ≤ Fm.CP → ∃ x₁ : ℝ, ∀ x (hx : Fm.x1 < x), x₁ ≤ x → ∀ i : Fm.Ix x, SizesAt (Fm.L x i) ∧ (Fm.params x hx i).CnW = 10 ∧ (∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1) ∧ 1000 ≤ (Fm.parT x hx i).CP ∧ (Fm.parT x hx i).CP ^ 20 ≤ zBase (Fm.L x i) ∧ DV.KapDef (Fm.D x i) ∧ Nonempty (ErrX (Fm.D x i)) ∧ (Fm.L x i).sc.x = x ∧ (JointQ (Fm.D x i) → FieldSmall (Fm.D x i) (Fm.L x i)) := by
  intro eps Fm hP hCP
  refine ⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩
  intro x hx hx₁ i
  have hS : SizesAt (Fm.L x i) := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hCnW : (Fm.params x hx i).CnW = 10 := (Fm.fixed.2.2.2.2.2.2.2 x hx i).1

  have hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1 := by
    intro k
    have hpr := (Fm.D x i).host.g_prime k
    have hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ) := by exact_mod_cast hpr.pos
    have hle := (hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k
    have := (Real.log_le_iff_le_exp hpos).2 hle
    linarith
  have h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x := by
    rw [hLx]; exact le_trans (le_max_left _ _) hx₁
  obtain ⟨hH, hF⟩ := hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60

  have hCPeq : (Fm.parT x hx i).CP = Fm.CP := by
    unfold FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  have hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L := hH.len

  have hf : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have hK := hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul] at hK
      have hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i) :=
        Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
      have := mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)
      linarith
    · exact_mod_cast hpos
  refine ⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩
  · rw [hCPeq]; exact hCP
  ·
    unfold zBase
    rw [hCPeq]
    have hr : x ≤ ((Fm.D x i).R.r : ℝ) := by
      have h := scale_le_rank hS
      rw [hLx] at h
      exact h
    have hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := Nat.cast_nonneg _
    have h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r := le_mul_of_one_le_left hr0 hf
    have h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [le_trans (le_max_right _ _) hx₁]
  · intro hJ
    exact hF (hJ.2.2.2.2 _ hH)

end GlobalTheory.FinalRows

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_coeff_deltaOK_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0) (p : ℕ) (I : Ideal (𝓞 E)), CoverOK d p I → RootOK d → (∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ) → ∃ φ : ∀ n, (Fin n → LevQ Dw d.l₂) → c.F, ∀ n, DeltaOK (GlobalTheory.FormTies.withCoeff d (φ n)) p I := by
  intro E _ _ _ H Dw l Xo c d p I hc hr ⟨ψ, hψ, ht⟩
  have key : ∀ n, ∃ φ : (Fin n → LevQ Dw d.l₂) → c.F, DeltaOK (GlobalTheory.FormTies.withCoeff d φ) p I := by
    intro n
    by_cases hn : Dw.p + Dw.q ≤ n
    · obtain ⟨φ, ph, x₀, h⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n
        (GlobalTheory.FormTies.withCoeff d (0 : (Fin n → LevQ Dw d.l₂) → c.F)) hc.2.2.1 hn ψ
      exact ⟨φ, hc, hr, fun _ => ⟨ph, ψ, x₀, hψ, h, ht⟩⟩
    · exact ⟨0, hc, hr, fun h => absurd h hn⟩
  choose φ hφ using key
  exact ⟨φ, hφ⟩

end GlobalTheory
end

section

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis
  GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

theorem exists_eigen_casOp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ →
    (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) →
    (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) →
    ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  intro n ε H _ _ _ σ d e X Y h hX hY hK
  have hσ := h.1
  obtain ⟨v₀, hv₀K, hv₀⟩ := h.2.2.2.2
  let f : KG ε → ℂ := fun k => star ⟪v₀, σ (toMK k) v₀⟫_ℂ
  have hfc : Continuous f := (continuous_const.inner (KCoef.continuous_orbit hσ v₀)).star
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ hfc
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h f (KCoef.kFinFun_coef hσ hv₀K)
  let Ss : Submodule ℂ H := smooth (Jm ε) σ
  let V : Submodule ℂ H := Ss.map (Q : H →ₗ[ℂ] H)
  have hVspan : V ≤ Submodule.span ℂ (Set.range a) := by
    rintro _ ⟨w, -, rfl⟩
    change Q w ∈ _
    rw [hQ, hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hVsm : ∀ u ∈ V, Sm ε σ u := by
    intro u hu
    have hspan : Submodule.span ℂ (Set.range a) ≤ Ss :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h.2.2.1 _ (haK j))
    exact hspan (hVspan hu)
  haveI : FiniteDimensional ℂ V :=
    by
      haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
      exact Submodule.finiteDimensional_of_le hVspan

  have hcomm : ∀ v, Sm ε σ v → casOp σ X Y (Q v) = Q (casOp σ X Y v) := by
    intro v hv
    have hQv : Sm ε σ (Q v) := hVsm _ ⟨v, hv, rfl⟩
    refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
    have hy' : Sm ε σ y := hy
    rw [inner_casOp hσ hX hY hy' hQv, hQ, hQ, KCoef.inner_kAvg hσ hfc, KCoef.inner_kAvg hσ hfc]
    congr 1
    funext k
    congr 1
    rw [← inner_casOp hσ hX hY hy' (Sm.translate hσ hv (KCoef.toMK_mem_UJ k)), hK _ (toMK_mem_K k) v hv]
  have hVmap : ∀ u ∈ V, casOp σ X Y u ∈ V := by
    rintro _ ⟨v, hv, rfl⟩
    change casOp σ X Y (Q v) ∈ V
    rw [hcomm v hv]
    exact ⟨_, sm_casOp hσ hX hY hv, rfl⟩
  let F : Module.End ℂ V :=
    { toFun := fun u => ⟨casOp σ X Y u, hVmap u u.2⟩
      map_add' := fun x y => Subtype.ext (casOp_add hσ hX hY (hVsm _ x.2) (hVsm _ y.2))
      map_smul' := fun r x => Subtype.ext (casOp_smul hσ hX hY r (hVsm _ x.2)) }
  have hQv₀ : Q v₀ ≠ 0 := by
    intro h0
    apply KCoef.inner_kAvg_ne_zero hσ hv₀
    rw [← hQ, h0, inner_zero_right]
  haveI : Nontrivial V := ⟨⟨⟨Q v₀, v₀, h.2.2.1 _ hv₀K, rfl⟩, 0, fun h0 => hQv₀ (congrArg Subtype.val h0)⟩⟩
  obtain ⟨χ, hχ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨u, hu⟩ := hχ.exists_hasEigenvector
  refine ⟨u, χ, hVsm _ u.2, fun h0 => hu.2 (Subtype.ext h0), ?_⟩
  exact congrArg Subtype.val (hu.apply_eq_smul)

end GlobalTheory.TypeSum.CasBasis

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KFourier
open MeasureTheory

theorem hs_nonneg' {n : ℕ} (y : Mx n) : 0 ≤ hs y := by
  show 0 ≤ ∑ i, ∑ j, ‖y i j‖ ^ 2
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem kFourier_coeff_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  intro n ε N F hD hG hC e he u hu
  obtain ⟨r, X, hX, hsp⟩ := GlobalTheory.T.exists_finite_real_spanning_compactLieAlgebra ε
  obtain ⟨c, α, hc, hα, hgap⟩ := GlobalTheory.T.compactUnitary_polynomial_spectral_gap ε X hX hsp
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (n : ℝ) ^ 2 + 2 < α * M := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((n : ℝ) ^ 2 + 2) / α)
    exact ⟨M, by rw [div_lt_iff₀ hα] at hM; linarith⟩
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX 0 u hu
  obtain ⟨C, hCM⟩ := GlobalTheory.T.compactUnitaryCasimir_pow_pairing_moderateGrowth_bound ε N F hD hG hC X hX M u hu
  have hlnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((c * x ^ α) ^ M)⁻¹ := fun x hx =>
    inv_nonneg.mpr (pow_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hx _)) _)
  let B : ℕ → ℝ := fun i => |C| * ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)
  refine ⟨fun i => if i = 0 then |C0| * Real.sqrt (Module.finrank ℂ (polyV ε 0)) else B i, ?_, ?_⟩
  · refine (summable_nat_add_iff 1).mp ?_
    have hp : (n : ℝ) ^ 2 - α * M < -1 := by linarith
    have hsm : Summable (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ ((n : ℝ) ^ 2 - α * M)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hsm.mul_left (|C| * (c ^ M)⁻¹ * 2 ^ (n ^ 2)))
    · simp only [Nat.add_one_ne_zero, if_false, B]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (hlnn _ (Nat.cast_nonneg _))) (by positivity)
    · simp only [Nat.add_one_ne_zero, if_false, B]
      set x : ℝ := ((i + 1 : ℕ) : ℝ) with hx
      have hx1 : 1 ≤ x := by simp [hx]
      have hx0 : 0 < x := by linarith
      have e1 : (c * x ^ α) ^ M = c ^ M * x ^ (α * M) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      have e2 : (x + 1) ^ (n ^ 2) ≤ 2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2) := by
        rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have e3 : x ^ ((n : ℝ) ^ 2 - α * M) = x ^ ((n : ℝ) ^ 2) * (x ^ (α * M))⁻¹ := by
        rw [Real.rpow_sub hx0, div_eq_mul_inv]
      rw [e1, e3, mul_inv]
      have h0 : 0 ≤ |C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le _)))
          (inv_nonneg.mpr (Real.rpow_nonneg hx0.le _))
      calc |C| * ((c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2)
          = (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (x + 1) ^ (n ^ 2) := by ring
        _ ≤ (|C| * (c ^ M)⁻¹ * (x ^ (α * M))⁻¹) * (2 ^ (n ^ 2) * x ^ ((n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left e2 h0
        _ = _ := by ring
  · intro i y hy
    have hy0 : 0 ≤ (1 + hs y) ^ N := pow_nonneg (by linarith [hs_nonneg' y]) _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [if_true]
      have h := hC0 0 (e 0) (he 0).1 y hy
      simp only [Function.iterate_zero, id] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε 0 (e 0) (he 0)
      calc _ ≤ C0 * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖e 0 k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C0| * (1 + hs y) ^ N * Real.sqrt (Module.finrank ℂ (polyV ε 0)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_le_sqrt hk)
              (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by ring
    · have hi0 : i ≠ 0 := hi.ne'
      simp only [hi0, if_false]
      have hl : 0 < c * (i : ℝ) ^ α := mul_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hi) _)
      obtain ⟨s, hsP, hse, hsn⟩ := GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound ε X hX i (c * (i : ℝ) ^ α) hl
        (fun p hp hq => hgap i hi p hp hq) M (e i) (he i).1
        (fun q hq => by rw [← (he i).2.1 q hq]; congr 1; funext k; ring)
      have h := hCM i s hsP y hy
      rw [hse] at h
      have hk := GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank ε i (e i) (he i)
      have hd : (Module.finrank ℂ (polyV ε i) : ℝ) ≤ ((i : ℝ) + 1) ^ (2 * n ^ 2) := by
        exact_mod_cast GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le ε i
      have hsq : Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) ≤
          ((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2) := by
        have h1 : ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2 := by
          calc _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * ∫ k, ‖e i k‖ ^ 2 ∂(muK ε) := hsn
            _ ≤ ((c * (i : ℝ) ^ α) ^ (2 * M))⁻¹ * (((i : ℝ) + 1) ^ (2 * n ^ 2)) :=
                mul_le_mul_of_nonneg_left (hk.trans hd) (inv_nonneg.mpr (pow_nonneg hl.le _))
            _ = _ := by rw [mul_pow ((c * (i : ℝ) ^ α) ^ M)⁻¹, inv_pow, ← pow_mul, ← pow_mul, mul_comm M 2, mul_comm (n ^ 2) 2]
        calc _ ≤ Real.sqrt ((((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) ^ 2) :=
              Real.sqrt_le_sqrt h1
          _ = _ := Real.sqrt_sq (mul_nonneg (hlnn _ (Nat.cast_nonneg _)) (by positivity))
      calc _ ≤ C * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) := h
        _ ≤ |C| * (1 + hs y) ^ N * Real.sqrt (∫ k, ‖s k‖ ^ 2 ∂(muK ε)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (Real.sqrt_nonneg _)
        _ ≤ |C| * (1 + hs y) ^ N * (((c * (i : ℝ) ^ α) ^ M)⁻¹ * ((i : ℝ) + 1) ^ (n ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (abs_nonneg _) hy0)
        _ = _ := by simp only [B]; ring

end GlobalTheory.KFourier
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.KProjApprox

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero' : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) := ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add' {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', max (max C C') 0, words_append hS hS', fun w hw => ?_⟩
  have e1 := hC w hw
  have e2 := hC' w hw
  have s1 : 0 ≤ sobNorm σ S w := sobNorm_nonneg σ S w
  have s2 : 0 ≤ sobNorm σ S' w := sobNorm_nonneg σ S' w
  have h3 : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := sobNorm_append σ S S' w
  change ‖ℓ w + ℓ' w‖ ≤ max (max C C') 0 * sobNorm σ (S ++ S') w
  change ‖ℓ w‖ ≤ C * sobNorm σ S w at e1
  change ‖ℓ' w‖ ≤ C' * sobNorm σ S' w at e2
  rw [h3]
  have a1 : C * sobNorm σ S w ≤ max (max C C') 0 * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) s1
  have a2 : C' * sobNorm σ S' w ≤ max (max C C') 0 * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) s2
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul' (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have e1 := hC w hw
  change ‖c * ℓ w‖ ≤ ‖c‖ * C * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left e1 (norm_nonneg c)

theorem sobCont_sum {ι : Type} (s : Finset ι) (ℓ : ι → (H →ₗ[ℂ] ℂ)) (h : ∀ i, Sobolev₂ (lieSet ε) σ (ℓ i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, ℓ i) :=
  Finset.sum_induction _ _ (fun _ _ => sobCont_add') sobCont_zero' fun i _ => h i

end GlobalTheory.TypeSum.KProjApprox

namespace GlobalTheory.TypeSum

open GlobalTheory.TypeSum.KProjApprox

theorem kAvg_approx_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
    ∃ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) ∧
      ∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε →
            ‖(∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) - ∑ a, L a (σ y (w a))‖ < δ := by
  intro n ε H _ _ _ σ h f hf happ e he hK
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h e hK
  refine ⟨m, a, haK, fun C hC δ hδ => ?_⟩
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  set I := ∫ k, ‖e k‖ ∂(muK ε) with hIdef
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hC' : IsCompact ((fun p : Mx n × KG ε => p.1 * toMK p.2) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul ((continuous_toMK ε).comp continuous_snd))
  obtain ⟨m', ℓ, v, hℓ, hv, happ'⟩ := happ _ hC' (δ / (1 + I)) (by positivity)
  refine ⟨fun j => ∑ i, ⟪c j, v i⟫_ℂ • ℓ i, fun j => sobCont_sum _ _ fun i => sobCont_smul' _ (hℓ i),
    fun y hy hyU => ?_⟩
  have hsm : ∀ w, Sm ε σ (kAvg ε σ e w) := fun w => h.2.2.1 _ (by
    rw [hsum]
    exact (kfin ε σ).sum_mem fun j _ => (kfin ε σ).smul_mem _ (haK j))
  have hmem : ∀ k : KG ε, y * toMK k ∈ UJset ε := fun k => mul_mem_UJ hyU (GlobalTheory.ExpansionAverage.toMK_mem k)
  have hcm : Continuous fun k : KG ε => y * toMK k := continuous_const.mul (continuous_toMK ε)
  have hci : ∀ i, Continuous fun k : KG ε => ℓ i (σ (y * toMK k) (v i)) := fun i =>
    (h.continuousOn_coef (hℓ i) (hv i)).comp_continuous hcm hmem
  have hcf : Continuous fun k : KG ε => f (y * toMK k) := hf.comp_continuous hcm hmem
  have h1 : ∀ i, ℓ i (σ y (kAvg ε σ e (v i))) = ∫ k, e k * ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    intro i
    have := GlobalTheory.ExpansionAverage.form_kAvg h he (sobCont_translate h.1 (hℓ i) hyU) (hv i) (hsm _)
    simpa [sigma_mul h.1 hyU (GlobalTheory.ExpansionAverage.toMK_mem _)] using this
  have hid : ∑ j, (∑ i, ⟪c j, v i⟫_ℂ • ℓ i) (σ y (a j)) =
      ∫ k, e k * ∑ i, ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum (f := fun i k => e k * ℓ i (σ (y * toMK k) (v i))) Finset.univ
      fun i _ => GlobalTheory.ExpansionAverage.integrable_K (he.mul (hci i))]

    simp_rw [← h1, hsum, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
  have hint : ∀ k : KG ε, ‖e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))‖ ≤ ‖e k‖ * (δ / (1 + I)) := by
    intro k
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (happ' _ ⟨(y, k), ⟨hy, Set.mem_univ _⟩, rfl⟩ (hmem k)).le (norm_nonneg _)
  have i1 : Integrable (fun k : KG ε => e k * f (y * toMK k)) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul hcf)
  have i2 : Integrable (fun k : KG ε => e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul (continuous_finsetSum _ fun i _ => hci i))
  rw [hid, ← integral_sub i1 i2]
  calc ‖∫ k, (e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) ∂(muK ε)‖
      ≤ ∫ k, ‖e k‖ * (δ / (1 + I)) ∂(muK ε) :=
        norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (he.norm.mul continuous_const))
          (Filter.Eventually.of_forall hint)
    _ = I * (δ / (1 + I)) := integral_mul_const _ _
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
end TypeSum
end GlobalTheory
end
end
