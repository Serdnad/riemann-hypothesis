module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle188
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | exact GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | (intros; apply GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (G : GlobalTheory.BK.Hom Q T), IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  first | exact @GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | exact GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | (intros; apply GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_E_smul_EN_mem_Man : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι),
    ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  have hk : 1 / ((e : ℝ) * l) < 1 / (e : ℝ) := by
    have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact one_div_lt_one_div_of_lt he (by nlinarith)

  have hL : ∀ v ∈ P.L, E K l e ^ α • P.conn v ∈ P.Man := by
    intro v hv
    have hv' : v ∈ P.Lk (1 / (e : ℝ)) := P.ext_mono (A_le_Rpi l e) hv
    obtain ⟨w, rfl⟩ := P.xiExt.surjective v
    have hw : w ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk w).1 hv'
    have hNw : (fun τ i => N K (w τ i)) ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      mem_tot.2 fun τ i => N_mem (derivative_mem_R l (mem_tot.1 hw τ i))
    have h1 : P.conn (P.xiExt w) ∈ P.ext (Rpi O K l e) := by
      rw [PhiMod.conn_xiExt]
      exact (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk _).2 hNw
    exact P.smul_mem_Mext_of_basis (fun i => hα _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_Rpi l e) h1
  refine ⟨α + β, fun m hm => ?_⟩
  have hv := hL _ (hβ m hm)
  rw [PhiMod.conn_smul, smul_add, smul_smul, smul_smul, ← pow_add] at hv
  have h2 : (E K l e ^ α * N K (E K l e ^ β)) • m ∈ P.Man :=
    P.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) α) (N_mem (derivative_mem_R l (pow_mem (E_mem l e _) β))))
      (P.M_le_Man hm)
  have h3 : E K l e ^ (α + β) • P.conn m ∈ P.Man := by
    have := sub_mem hv h2
    rwa [add_sub_cancel_left] at this
  rw [PhiMod.EN_apply, smul_comm]
  exact P.smul_mem_Man (E_mem l e _) h3

end GlobalTheory.BK
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wach_lattice_free_of_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(Mo.N T)) := by
  first | exact @GlobalTheory.HWL.lattice_free | exact GlobalTheory.HWL.lattice_free | (intros; apply GlobalTheory.HWL.lattice_free <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  first | exact @GlobalTheory.PhiGam.PolarKernel.main | exact GlobalTheory.PhiGam.PolarKernel.main | (intros; apply GlobalTheory.PhiGam.PolarKernel.main <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  first | exact @GlobalTheory.PhiGam.PolarCount.main | exact GlobalTheory.PhiGam.PolarCount.main | (intros; apply GlobalTheory.PhiGam.PolarCount.main <;> assumption)
end

section

open GlobalTheory.BK PowerSeries

namespace GlobalTheory.BK

theorem PhiMod.pow_smul_phi_mem_MM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (η : ℕ)
    (h : ∀ m ∈ P.L, E K l e ^ η • m ∈ P.M) :
    ∀ m ∈ P.MM, (l : K) ^ η • P.phi m ∈ P.MM := by
  intro m hm
  have h1 : E K l e ^ η • m ∈ P.Mext (S O K e) :=
    P.smul_mem_Mext_of_basis (fun i => h _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_S l e) hm
  have h2 := P.phi_mem_ext (fun _ => frob_mem_S l) h1
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have h3 := (P.ext (S O K e)).smul_mem (⟨c ^ η, pow_mem hc η⟩ : S O K e) h2
  rw [Subalgebra.smul_def, P.phi_smul, smul_smul, map_pow, ← mul_pow, hcE] at h3
  have h4 : ((l : K⟦X⟧) ^ η) • P.phi m = (l : K) ^ η • P.phi m := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [h4] at h3

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK.IntegralLeftInverseExactTriple

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem mem_M_single (P : PhiMod O K l e a ι) (τ : ZMod a) (u : ι → K⟦X⟧)
    (hu : ∀ i, u i ∈ A O K) : (Pi.single τ u : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun σ => mem_vecs.2 fun i => ?_
  by_cases h : σ = τ
  · subst h; simpa using hu i
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem app_single {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (τ : ZMod a)
    (u : ι → K⟦X⟧) : F.app (Pi.single τ u) = Pi.single τ (F.mat τ *ᵥ u) := by
  funext σ
  rw [Hom.app_apply]
  by_cases h : σ = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_one_mem (ν : Type) [Fintype ν] [DecidableEq ν] (n : ℕ) (i j : ν) :
    (((l : K) ^ n) • (1 : Matrix ν ν K⟦X⟧)) i j ∈ A O K := by
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · rw [show ((l : K) ^ n) • (1 : K⟦X⟧) = ((l ^ n : ℕ) : K⟦X⟧) by simp [Algebra.smul_def]]
    exact natCast_mem _ _
  · rw [smul_zero]; exact zero_mem _

end GlobalTheory.BK.IntegralLeftInverseExactTriple

namespace GlobalTheory.BK


open IntegralLeftInverseExactTriple in
theorem exists_integral_leftInverse_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG n hG τ
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  have hGF : G.mat τ * F.mat τ = 0 := by
    refine Matrix.ext fun i j => ?_
    have hs := mem_M_single P τ (Pi.single j 1) fun i' => by
      by_cases h : i' = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 := (hFG.exact _ (F.app_mem_M hs)).2 ⟨_, hs, rfl⟩
    have := congrFun (congrFun h0 τ) i
    rw [app_single, app_single, Pi.single_eq_same, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      at this
    simpa using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, hWA, ?_⟩
  have hFWF : F.mat τ * (W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hFW]
    simp only [Z, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hGF,
      Matrix.mul_zero, sub_zero, Matrix.mul_smul, Matrix.mul_one, sub_self]
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => ?_
  set D := W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧) with hD
  have hDm : Pi.single τ (fun i' => D i' j) ∈ P.M := mem_M_single P τ _ fun i' =>
    sub_mem (Subalgebra.sum_mem _ fun k _ => mul_mem (hWA i' k) (F.mem _ _ _)) (smul_one_mem ι n i' j)
  have hFD : F.mat τ *ᵥ (fun i' => D i' j) = 0 := by
    funext k
    have := congrFun (congrFun hFWF k) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h0 := hFG.inj _ hDm (by rw [app_single, hFD, Pi.single_zero])
  have := congrFun (congrFun h0 τ) i
  simpa using this

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mixedModel_weylElement_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  first | exact @GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | exact GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | (intros; apply GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O, ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.trace_int | exact GlobalTheory.UnitLemma.Unr.trace_int | (intros; apply GlobalTheory.UnitLemma.Unr.trace_int <;> assumption)
end
