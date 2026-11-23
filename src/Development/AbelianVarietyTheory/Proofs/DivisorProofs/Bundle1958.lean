module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Formalism.LocalToGlobal.Columns.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isAmpleLB_pull_fst_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  intro R _ _ A _ hA L hL c V hc hV hloc T _ n a hcov hrel
  haveI : IsProper A.hom := hA.proper
  have hL' : (L.pull (fst A T).left).IsLB := LB.isLB_pull hL _
  have h2 : (lbPow (L.pull (fst A T).left) 2).IsLB := GlobalTheory.isLB_lbPow hL' 2
  have hcls : cls _ h2 = 2 • CechPic.pull (fst A T).left c := by
    rw [cls_lbPow hL' 2 h2, cls_pull hL _ hL', hc]
  have hsec : ∀ i, ∃ s : (lbPow (L.pull (fst A T).left) 2).Sec, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s =
      (fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V := fun i =>
    IsLocus.exists_sec h2 (hcls ▸ GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square (Sp R) A hA c V hloc T (a i) (hrel i))
  choose s hs using hsec
  exact isAmpleLB_of_cover hL' (by norm_num) s (by simp only [hs]; exact hcov)
    fun i => (hs i).symm ▸ GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme R A V hV T (a i)

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnrSat

theorem eventually_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B := by
  intro hF E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  filter_upwards [LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))] with w hw
  refine exists_hasSatGL_locRep hF E a π w
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ?_, fun e => h0 (congrArg Subtype.val e)⟩)
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.UnrSat
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_rapidDecay_siegel : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  intro hP E _ _ _ a ψ hψ Ω hΩ t ht lam
  obtain ⟨N, hN⟩ := GlobalTheory.T.automorphicForm_GL_uniform_moderate_growth hP E a ψ hψ.1
  obtain ⟨m, C1, hC1, hreal⟩ := GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character a t ht lam N
  obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
  obtain ⟨C0, hC0⟩ := hN []
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at hC0
  have hC0' : ∀ y, ‖ψ.1 (infGL E a y)‖ ≤ max C0 0 * height y ^ N := fun y =>
    (hC0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith [one_le_height y]) _))
  have hex : ∀ i j : Fin a, ∃ C : ℝ, 0 ≤ C ∧ ((j : ℕ) = i + 1 → ∀ (r : Fin a → ℝ)
      (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
      ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N) := by
    intro i j
    by_cases hij : (j : ℕ) = i + 1
    · obtain ⟨C, hC, h⟩ := GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth hP E a N t ht i j hij m ψ hψ hN Ω hΩ
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hij⟩
  choose Cf hCf0 hCf using hex
  have hS0 : 0 ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 := Finset.sum_nonneg fun p _ => hCf0 p.1 p.2
  have hK0 : 0 ≤ max C0 0 * B ^ N := mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _)
  refine ⟨(max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1,
    mul_nonneg (add_nonneg hK0 hS0) hC1, ?_⟩
  intro r d hr hrt hd hprod c hc
  have hhd : height d ^ N ≤ (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N :=
    pow_le_pow_left₀ (by linarith [one_le_height d]) (GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv E a r d hr hd) N
  have hP0 : 0 ≤ ∏ i, r i ^ lam i := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _
  have hsplit : (max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1 * ∏ i, r i ^ lam i
      = max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i)
        + (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) := by ring
  have hA := mul_nonneg hK0 (mul_nonneg hC1 hP0)
  have hB' := mul_nonneg hS0 (mul_nonneg hC1 hP0)
  rcases hreal r hr hrt hprod with h1 | ⟨i, j, hij, h2⟩
  · have hdc : height (d * c) ^ N ≤ (B * height d) ^ N :=
      pow_le_pow_left₀ (by linarith [one_le_height (d * c)]) (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ max C0 0 * height (d * c) ^ N := hC0' _
      _ ≤ max C0 0 * (B * height d) ^ N := mul_le_mul_of_nonneg_left hdc (le_max_right _ _)
      _ = max C0 0 * B ^ N * height d ^ N := by rw [mul_pow]; ring
      _ ≤ max C0 0 * B ^ N * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N := mul_le_mul_of_nonneg_left hhd hK0
      _ ≤ max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := by rw [hsplit]; linarith
  · have hq : 0 ≤ (r j / r i) ^ m := pow_nonneg (div_nonneg (hr j).le (hr i).le) _
    have hle : Cf i j ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 :=
      Finset.single_le_sum (f := fun p : Fin a × Fin a => Cf p.1 p.2) (fun p _ => hCf0 p.1 p.2)
        (Finset.mem_univ (i, j))
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ Cf i j * (r j / r i) ^ m * height d ^ N :=
          hCf i j hij r d hr hrt hd c hc
      _ ≤ Cf i j * ((r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhd hq) (hCf0 i j)
      _ ≤ Cf i j * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h2 (hCf0 i j)
      _ ≤ (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hC1 hP0)
      _ ≤ _ := by rw [hsplit]; linarith

end GlobalTheory
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.SiegelSet

theorem isRealLine_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∀ s t, γ (s + t) = γ s * γ t := by
  intro F E _ _ _ _ _ σ hCM n J γ hγ s t
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  obtain ⟨y1, e1, f1⟩ := hγ (s + t)
  obtain ⟨y2, e2, f2⟩ := hγ s
  obtain ⟨y3, e3, f3⟩ := hγ t
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply (archEquiv J hCM τ).injective
  apply Subtype.ext
  apply Units.ext
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv, ← GlobalTheory.Orb.archMat_eq_archEquiv, map_mul, f1, f2, f3, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl Z).smul_left s |>.smul_right t)

end GlobalTheory.SiegelSet
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.RealLineCont

theorem continuous_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ → Continuous γ := by
  intro F E _ _ _ _ _ σ h n J γ ⟨w, τ, Z, _, hy⟩
  choose y hγ hy using hy
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
    have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
      funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
    rw [e]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
      letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
  have : γ = fun t => embArch σ J w (y t) := funext hγ
  rw [this]
  exact (continuous_embArch σ J w).comp hc

end GlobalTheory.RealLineCont
end

section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RealLineInf

theorem realLine_mem_infPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (β : ℝ → GAd σ J), IsRealLine σ J β → ∀ t, β t ∈ infPts σ J := by
  intro F E _ _ _ _ _ σ n J β hβ t
  obtain ⟨w, τ, Z, -, h⟩ := hβ
  obtain ⟨y, hy, -⟩ := h t
  rw [hy]
  exact mem_infPts.2 (projFin_embArch σ J w y)

end GlobalTheory.RealLineInf
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.UAut

theorem exists_coordSecondKind_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ),
      (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧
        ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  intro F E _ _ _ _ _ σ h n J hJ w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _

  have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy

  have hS : ∀ g : GArch σ J w, GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
    intro g
    have := (archEquiv J h τ g).2
    rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact this
  have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1) (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
    simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j => GlobalTheory.Orb.archMat σ J τ b i j
      rw [e])
  refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
    fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
  filter_upwards [hc.eventually hev] with g hg
  have e1 : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
      embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  rw [e1]
  congr 1
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine hg.trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)

end GlobalTheory.UAut
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.InfChartConcat

theorem concat {G X ι : Type*} [Monoid G] (l : Filter X) (P : (ℝ → G) → Prop)
    (d : ι → ℕ) (η : ∀ j, Fin (d j) → ℝ → G) (s : ∀ j, X → Fin (d j) → ℝ)
    (hP : ∀ j i, P (η j i)) (hs : ∀ j, Tendsto (s j) l (𝓝 0)) :
    ∀ L : List ι, ∃ (m : ℕ) (η' : Fin m → ℝ → G) (s' : X → Fin m → ℝ),
      (∀ i, P (η' i)) ∧ Tendsto s' l (𝓝 0) ∧
      ∀ x, (List.ofFn fun i => η' i (s' x i)).prod =
        (L.map fun j => (List.ofFn fun i => η j i (s j x i)).prod).prod := by
  intro L
  induction L with
  | nil => exact ⟨0, Fin.elim0, fun _ => Fin.elim0, fun i => i.elim0,
      tendsto_pi_nhds.2 fun i => i.elim0, fun x => by simp⟩
  | cons j L ih =>
    obtain ⟨m, η', s', hP', hs', he⟩ := ih
    refine ⟨d j + m, Fin.append (η j) η', fun x => Fin.append (s j x) (s' x), ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hP j i
      · simpa using hP' i
    · rw [tendsto_pi_nhds]
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have := ((continuous_apply i).tendsto _).comp (hs j)
        simpa [Function.comp_def] using this
      · have := ((continuous_apply i).tendsto _).comp hs'
        simpa [Function.comp_def] using this
    · intro x
      have hf : (fun i => Fin.append (η j) η' i (Fin.append (s j x) (s' x) i)) =
          Fin.append (fun i => η j i (s j x i)) (fun i => η' i (s' x i)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      rw [hf, List.ofFn_fin_append, List.prod_append, he x]
      simp

theorem prod_map_ite_eq {ι M : Type*} [DecidableEq ι] [Monoid M] (u : ι) (a : M) (L : List ι) :
    (L.map fun w => if w = u then a else 1).prod = a ^ L.count u := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : w = u
    · subst h; simp [pow_succ']
    · simp [h]

theorem decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {x : GAd σ J} (hx : x ∈ infPts σ J) :
    x = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => embArch σ J w (projArch σ J w x)).prod := by
  classical
  apply GAd_ext σ J
  · intro u
    rw [map_list_prod, List.map_map]
    have hf : (projArch σ J u ∘ fun w => embArch σ J w (projArch σ J w x)) =
        fun w => if w = u then projArch σ J u x else 1 := by
      funext w
      by_cases h : w = u
      · subst h; simp
      · simp [h, projArch_embArch_ne σ J (Ne.symm h)]
    rw [hf, prod_map_ite_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ _)), pow_one]
  · intro v
    rw [map_list_prod, List.map_map, (mem_infPts_iff_forall).1 hx v]
    simp [Function.comp_def]

end GlobalTheory.InfChartConcat

theorem GlobalTheory.infPts_secondKind_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ),
    (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
    Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
    ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  intro F E _ _ _ _ _ σ hCM n J hJ
  classical
  have hp : ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J)
      (s : GArch σ J w → Fin d → ℝ), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1
    obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
    have hd : IsUnit A.det := by
      rw [show A = J.map τ.1 from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (IsUnit.mk0 _ hJ.2).map _
    have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w,
        GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
      intro i t
      obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
      have hskew : (t • Z i)ᴴ * A + A * (t • Z i) = 0 := by
        rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
          hZ i, smul_zero]
      have hpres := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd hskew
      refine ⟨(archEquiv J hCM τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ hpres⟩, ?_⟩
      rw [GlobalTheory.Orb.archMat_eq_archEquiv J hCM, MulEquiv.apply_symm_apply]
      exact hu
    choose y hy using hy
    have hS (g : GArch σ J w) :
        GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
      rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J hCM]
      exact (archEquiv J hCM τ g).2
    have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1)
        (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
      simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
    have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
      (GlobalTheory.Orb.isEmbedding_archMat J hCM τ).injective (by
        show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j =>
          GlobalTheory.Orb.archMat σ J τ b i j
        rw [e])
    refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
      fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
    filter_upwards [hc.eventually hev] with g hg
    have e : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
        embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [e]
    congr 1
    apply hinj
    rw [map_list_prod, List.map_ofFn]
    refine hg.trans (congrArg List.prod ?_)
    exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)
  choose d η s hη hs he using hp
  have hproj : ∀ w, Tendsto (projArch σ J w) (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 1) := fun w => by
    have := (continuous_projArch σ J w).tendsto 1
    rw [map_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨m, η', s', hP', hs', heq⟩ := GlobalTheory.InfChartConcat.concat
    (𝓝[(infPts σ J : Set (GAd σ J))] 1) (GlobalTheory.SiegelSet.IsRealLine σ J) d η
    (fun w x => s w (projArch σ J w x)) hη (fun w => (hs w).comp (hproj w))
    (Finset.univ : Finset (InfinitePlace F)).toList
  refine ⟨m, η', s', hP', hs', ?_⟩
  have hev : ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, ∀ w, embArch σ J w (projArch σ J w x) =
      (List.ofFn fun i => η w i (s w (projArch σ J w x) i)).prod :=
    Filter.eventually_all.2 fun w => (hproj w).eventually (he w)
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hmem
  rw [heq x, List.map_congr_left (fun w _ => (hx w).symm)]
  exact GlobalTheory.InfChartConcat.decomp σ J hmem
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.witt_frame_extends_to_block_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  first | exact @GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | exact GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis | (intros; apply GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.classSum_le_frameNorm_sq_good_part : ∀ (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (Pr : Primes X) (R : Ranks) (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) (P : LevFam X.E X.K R.r Pr.vGs) (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) (t : TupF TU) (hP : (mtildeGSD W Ch sel t.1 P).Ok), (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.Ok3 1 → ∀ (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) (F' : (mtildeKGSD W Ch sel t.1).EqFun), F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun → HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F') (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r (lvlIdem ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ)).mulVec ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ * ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) → ∀ (v : InfinitePlace X.K) (X0 : InfinitePlace X.K → Matrix (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) ℂ), IsUnit (X0 v).det → ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).HV t).map v.embedding → ((mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 := by
  first | exact @GlobalTheory.ClassSumLevel.classSum_le_normAt_sq | exact GlobalTheory.ClassSumLevel.classSum_le_normAt_sq | (intros; apply GlobalTheory.ClassSumLevel.classSum_le_normAt_sq <;> assumption)
end
