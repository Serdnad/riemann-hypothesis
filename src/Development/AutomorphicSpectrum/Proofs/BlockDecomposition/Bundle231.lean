module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle219
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle209
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerExt

section
variable {W : Type} [CommRing W] (l : ℕ) {A : Type} [CommRing A] [Algebra W A]
  {M : Type*} [AddCommGroup M] [Module W M]

theorem pow_smul_tmul (n : ℕ) (a : A) (m : M) :
    ((l : A) ^ n) • (a ⊗ₜ[W] m) = a ⊗ₜ[W] (((l : W) ^ n) • m) := by
  have h : ((l : W) ^ n) • a = (l : A) ^ n * a := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [← TensorProduct.smul_tmul, h, TensorProduct.smul_tmul', smul_eq_mul]

theorem pow_smul_eq_zero (n : ℕ) (h : ∀ x : M, ((l : W) ^ n) • x = 0) (t : A ⊗[W] M) :
    ((l : A) ^ n) • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [pow_smul_tmul, h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem lTensor_pow_smul (n : ℕ) (v : A ⊗[W] M) :
    LinearMap.lTensor A (((l : W) ^ n) • (LinearMap.id : M →ₗ[W] M)) v = ((l : A) ^ n) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [pow_smul_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

theorem mem_pow_smul_top {N : Type*} [AddCommGroup N] [Module A N] (n : ℕ) (v : N) :
    v ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A N) ↔ ∃ u : N, v = ((l : A) ^ n) • u := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, Submodule.mem_top, rfl⟩
end

section
variable {W : Type} [CommRing W] (l : ℕ) (S : Sys.{1} W) (A : Type) [CommRing A] [Algebra W A]

theorem r_baseChange_pr (n : ℕ) (w : A ⊗[W] S.lim) :
    (S.r n).baseChange A ((pr S (n + 1)).baseChange A w) = (pr S n).baseChange A w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have hx : S.r n (x.1 (n + 1)) = x.1 n := x.2 n
    simp only [LinearMap.baseChange_tmul]
    change a ⊗ₜ[W] S.r n (x.1 (n + 1)) = a ⊗ₜ[W] x.1 n
    rw [hx]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_eq_pow_smul [Module.Flat W A] (n : ℕ)
    (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : (pr S n).baseChange A w = 0) :
    ∃ v : A ⊗[W] S.lim, w = ((l : A) ^ n) • v := by
  have hex : Function.Exact (((l : W) ^ n) • (LinearMap.id : S.lim →ₗ[W] S.lim)) (pr S n) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hker x hx
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      change (pr S n) (((l : W) ^ n) • y) = 0
      rw [map_smul]
      exact hkill _
  have hw' : (LinearMap.lTensor A (pr S n)) w = 0 := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact hw
  obtain ⟨v, rfl⟩ := (Module.Flat.lTensor_exact A hex w).1 hw'
  exact ⟨v, lTensor_pow_smul l n v⟩

theorem baseChange_pr_pow_smul (n : ℕ) (hkill : ∀ (x : S.M n), ((l : W) ^ n) • x = 0)
    (u : A ⊗[W] S.lim) : (pr S n).baseChange A (((l : A) ^ n) • u) = 0 := by
  rw [map_smul]
  exact pow_smul_eq_zero l n hkill _

theorem exists_baseChange_pr_eq (n c : ℕ)
    (hcok : ∀ (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) (t : A ⊗[W] S.M n) :
    ∃ w : A ⊗[W] S.lim, (pr S n).baseChange A w = ((l : A) ^ c) • t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨y, hy⟩ := hcok m
    refine ⟨a ⊗ₜ[W] y, ?_⟩
    rw [pow_smul_tmul, ← hy, LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨w₁, h₁⟩ := hx
    obtain ⟨w₂, h₂⟩ := hy
    exact ⟨w₁ + w₂, by rw [map_add (f := _), h₁, h₂, smul_add]⟩

theorem eq_zero_of_baseChange_pr [Module.Flat W A]
    [IsHausdorff (Ideal.span {(l : A)}) (A ⊗[W] S.lim)]
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (w : A ⊗[W] S.lim) (hw : ∀ n, (pr S n).baseChange A w = 0) : w = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance w fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top]
  exact exists_eq_pow_smul l S A n (hkill n) (hker n) w (hw n)

theorem exists_lift [Module.Flat W A]
    [IsPrecomplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim)] (c : ℕ)
    (hkill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0)
    (hker : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (hcok : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x)
    (z : ∀ n, A ⊗[W] S.M n) (hz : ∀ n, (S.r n).baseChange A (z (n + 1)) = z n) :
    ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w = ((l : A) ^ c) • z n := by
  choose f hf using fun n => exists_baseChange_pr_eq l S A n c (hcok n) (z n)
  have hstep : ∀ n, f n ≡ f (n + 1) [SMOD ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro n
    rw [SModEq.sub_mem, mem_pow_smul_top]
    refine exists_eq_pow_smul l S A n (hkill n) (hker n) _ ?_
    rw [map_sub, ← r_baseChange_pr S A n (f (n + 1)), hf (n + 1), map_smul, hz, hf n, sub_self]
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((Ideal.span {(l : A)}) ^ m • ⊤ : Submodule A (A ⊗[W] S.lim))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem] at *
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) ((SModEq.sub_mem).1 (hstep n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance hmono
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, mem_pow_smul_top] at h
  obtain ⟨u, hu⟩ := h
  have h0 : (pr S n).baseChange A (f n - L) = 0 := by
    rw [hu]
    exact baseChange_pr_pow_smul l S A n (hkill n) u
  rw [map_sub, sub_eq_zero, hf n] at h0
  exact h0.symm

end

theorem limit_extension_upTo : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (S : Sys.{1} W) (c : ℕ), Module.Finite W S.lim → (∀ n (x : S.M n), ((l : W) ^ n) • x = 0) → (∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y) → (∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A], (∀ w : A ⊗[W] S.lim, (∀ n, (pr S n).baseChange A w = 0) → w = 0) ∧ ∃ α : (tens A S).lim →ₗ[A] A ⊗[W] S.lim, ∀ z n, (pr S n).baseChange A (α z) = ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := by
  intro W _ _ _ l hl S c hfin hkill hker hcok A _ _ _ _
  haveI hcompl : IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] S.lim) :=
    GlobalTheory.T.adic_complete_tensor_finite W l hl A S.lim
  have hinj := eq_zero_of_baseChange_pr l S A hkill hker
  refine ⟨hinj, ?_⟩
  have hlift : ∀ z : (tens A S).lim, ∃ w : A ⊗[W] S.lim, ∀ n, (pr S n).baseChange A w =
      ((l : A) ^ c) • (z.1 n : A ⊗[W] S.M n) := fun z =>
    exists_lift l S A c hkill hker hcok (fun n => z.1 n) fun n => z.2 n
  choose g hg using hlift
  refine ⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hg⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, map_add (f := _), hg, hg, hg]
    exact sub_eq_zero.2 (smul_add ((l : A) ^ c) (x.1 n : A ⊗[W] S.M n) (y.1 n : A ⊗[W] S.M n))
  · rw [← sub_eq_zero]
    refine hinj _ fun n => ?_
    rw [map_sub, RingHom.id_apply, map_smul, hg, hg]
    exact sub_eq_zero.2 (smul_comm ((l : A) ^ c) a (x.1 n : A ⊗[W] S.M n))

end GlobalTheory.CompanionTheory.TowerExt
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasad

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead _root_.Topology

theorem lowC_central_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ U ∈ 𝓝 (1 : GL (Fin n) k),
    ∃ t : Levi k (fun a => Fin (d a)), (∀ m, t * m = m * t) ∧
      ∀ c ∈ lowC k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro k _ _ _ _ n s d e U hU
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k), Units.val ⁻¹' V ⊆ U := by
    rw [(isEmbedding_val_GL (k := k) n).nhds_eq_comap] at hU
    simpa using Filter.mem_comap.mp hU
  obtain ⟨W, hW, hWV⟩ := exists_entry_nhds hV
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).mp hW
  obtain ⟨c, hc0, hcγ, hc1⟩ : ∃ c : k, c ≠ 0 ∧ ValuativeRel.valuation k c < γ ∧
      ValuativeRel.valuation k c ≤ 1 := by
    obtain ⟨x, hx0, hx1⟩ := (Valuation.IsNontrivial.exists_lt_one : ∃ x : k, x ≠ 0 ∧ ValuativeRel.valuation k x < 1)
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := k) (γ : ValuativeRel.ValueGroupWithZero k)
    have hy0 : (0 : ValuativeRel.ValueGroupWithZero k) < ValuativeRel.valuation k y := by
      rw [hy]; exact Units.zero_lt γ
    rcases le_or_gt (ValuativeRel.valuation k y) 1 with hy1 | hy1
    · refine ⟨y * x, ?_, ?_, ?_⟩
      · exact mul_ne_zero (by rintro rfl; simp at hy0) hx0
      · rw [map_mul, ← hy]; exact mul_lt_of_lt_one_right hy0 hx1
      · rw [map_mul]; first | exact mul_le_one' hy1 hx1.le | exact mul_le_one₀ hy1 zero_le' hx1.le
    · refine ⟨x, hx0, ?_, hx1.le⟩
      rw [← hy]; exact hx1.trans hy1
  refine ⟨blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1), blockScalar_central hc0 _, ?_⟩
  intro g hg
  simp only [lowC, Set.mem_ofPred_eq] at hg
  obtain ⟨hK, hlow⟩ := hg
  have hgint : ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.mp hK
    intro i j
    exact (h i j).2
  have h0W : (0 : k) ∈ W := mem_of_mem_nhds hW
  have hdiag : leviEmb k e (blockScalar hc0 (GlobalTheory.DepthZeroJac.expo s 1)) =
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) := by
    refine Units.ext ?_
    rw [GlobalTheory.DepthZeroJac.dia_val]
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      show ((c ^ GlobalTheory.DepthZeroJac.expo s 1 a) •
        (1 : Matrix (Fin (d a)) (Fin (d a)) k)) i' j' = _
      by_cases h2 : i' = j'
      · subst h2
        simp
      · rw [Matrix.smul_apply, Matrix.one_apply_ne h2, smul_zero, Matrix.diagonal_apply_ne]
        simpa using h2
    · rw [leviEmb_apply_ne k e _ h, Matrix.diagonal_apply_ne]
      exact fun h' => h (congrArg Sigma.fst (e.injective h'))
  rw [hdiag]
  refine hVU (hWV _ fun i j => ?_)
  have hentry : (((GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1))⁻¹ * g *
      GlobalTheory.DepthZeroJac.dia e hc0 (GlobalTheory.DepthZeroJac.expo s 1) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
      = (c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e i))⁻¹ * (g : Matrix (Fin n) (Fin n) k) i j *
          c ^ GlobalTheory.DepthZeroJac.expo s 1 (blk e j) := by
    simp [GlobalTheory.DepthZeroJac.dia, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Matrix.sub_apply, hentry]
  by_cases hij : blk e j < blk e i
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero]
    apply hγ
    exact ((valuation_conj_le hc0 hc1 (hgint i j) (GlobalTheory.CompanionTheory.MoyPrasad.expo_gap 1 hij)).trans_eq
      (pow_one _)).trans_lt hcγ
  · have h0 := hlow i j hij
    rw [Matrix.sub_apply, sub_eq_zero] at h0
    rw [h0]
    by_cases hij' : i = j
    · subst hij'
      simpa [hc0] using h0W
    · simpa [Matrix.one_apply_ne hij'] using h0W

end GlobalTheory.CompanionTheory.MoyPrasad

end
end

section

noncomputable section

open Filter Topology
open scoped ZeroAtInfty InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FcCut

open PositivityTheory.RgBcC.Fc

def mulC (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ) (hf : ∀ y, R ≤ |y| → a y * f y = 0) :
    C₀(ℝ, ℂ) :=
  ⟨⟨fun y => a y * f y, ha.mul f.continuous⟩, by
    have hK : (Set.Icc (-R) R)ᶜ ∈ cocompact ℝ := isCompact_Icc.compl_mem_cocompact
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
    filter_upwards [hK] with y hy
    have hR : R ≤ |y| := by
      by_contra hlt
      push_neg at hlt
      exact hy ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    show (0 : ℂ) = a y * f y
    rw [hf y hR]⟩

@[simp] theorem mulC_apply (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ)
    (hf : ∀ y, R ≤ |y| → a y * f y = 0) (y : ℝ) : mulC a ha f R hf y = a y * f y := rfl

section Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem inner_star_mul (F : FCalc H M Ω T) (x : H) (a b : C₀(ℝ, ℂ)) :
    ⟪F.Φ (star a * b) x, x⟫_ℂ = ⟪F.Φ b x, F.Φ a x⟫_ℂ := by
  rw [F.map_mul, F.map_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem core (F : FCalc H M Ω T) (c : ℝ) (x : H)
    (hyp : ∀ g, ∃ v : M, (v : H) = F.Φ g x ∧ (⟪(Ω v : H), v⟫_ℂ).re ≤ c * ‖(v : H)‖ ^ 2)
    (f : C₀(ℝ, ℂ)) (δ R : ℝ) (hδ : 0 < δ) (h1 : ∀ y, y ≤ c + δ → f y = 0)
    (h2 : ∀ y, R ≤ |y| → f y = 0) : F.Φ f x = 0 := by
  let h := mulC (fun y => (y : ℂ)) Complex.continuous_ofReal f R
    (fun y hy => by rw [h2 y hy, mul_zero])
  let r := mulC (fun y => ((Real.sqrt (max (y - c - δ) 0) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (by fun_prop)) f R (fun y hy => by rw [h2 y hy, mul_zero])
  obtain ⟨v, hv, hle⟩ := hyp f
  have hΩ : (Ω v : H) = F.Φ h x := F.omega f h (fun y => rfl) x v hv
  have hid : star r * r = star f * h - ((c + δ : ℝ) : ℂ) • (star f * f) := by
    ext y
    by_cases hy : y ≤ c + δ
    · simp [r, h, h1 y hy]
    · have hpos : 0 ≤ y - c - δ := by linarith [not_le.mp hy]
      have hs : ((Real.sqrt (y - c - δ) : ℝ) : ℂ) * ((Real.sqrt (y - c - δ) : ℝ) : ℂ)
          = (y : ℂ) - c - δ := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]; push_cast; ring
      simp only [r, h, ZeroAtInftyContinuousMap.coe_mul, ZeroAtInftyContinuousMap.coe_star,
        ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul, Pi.mul_apply, Pi.star_apply,
        Pi.sub_apply, Pi.smul_apply, mulC_apply, max_eq_left hpos, star_mul', smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      linear_combination ((starRingEnd ℂ) (f y) * f y) * hs
  have e : ((‖F.Φ r x‖ ^ 2 : ℝ) : ℂ) = ⟪(Ω v : H), v⟫_ℂ - ((c + δ : ℝ) : ℂ) * ((‖(v : H)‖ ^ 2 : ℝ) : ℂ) := by
    have a1 := inner_star_mul F x r r
    have a2 := inner_star_mul F x f h
    have a3 := inner_star_mul F x f f
    rw [hid, map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, inner_smul_left, a2, a3, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at a1
    rw [hΩ, hv]
    push_cast
    simpa using a1.symm
  have e' := congrArg Complex.re e
  rw [Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at e'
  have hn : ‖(v : H)‖ ^ 2 ≤ 0 := by
    have p1 : 0 ≤ ‖F.Φ r x‖ ^ 2 := by positivity
    nlinarith
  have hv0 : ‖(v : H)‖ = 0 := by
    have := sq_nonneg ‖(v : H)‖
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn this)
  rw [← hv]
  exact norm_eq_zero.mp hv0

theorem approx (c : ℝ) (g : C₀(ℝ, ℂ)) (hg : ∀ y, y ≤ c → g y = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : C₀(ℝ, ℂ)) (δ R : ℝ), 0 < δ ∧ (∀ y, y ≤ c + δ → f y = 0) ∧ (∀ y, R ≤ |y| → f y = 0) ∧
      ‖g - f‖ ≤ 2 * ε := by

  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y, R ≤ |y| → ‖g y‖ ≤ ε := by
    have ht : Tendsto g (cocompact ℝ) (𝓝 0) := g.zero_at_infty'
    have hm : {y | ‖g y‖ < ε} ∈ cocompact ℝ := by
      have := ht (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.ball, dist_zero_right] using this
    obtain ⟨t, ht1, ht2⟩ := Filter.mem_cocompact.mp hm
    obtain ⟨r, hr⟩ := ht1.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨r + 1, fun y hy => ?_⟩
    have hyt : y ∈ tᶜ := fun hyt => by
      have := hr hyt
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    exact (ht2 hyt).le

  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ y, y ≤ c + δ → ‖g y‖ ≤ ε := by
    obtain ⟨d, hd, hdc⟩ := Metric.continuous_iff.mp g.continuous c ε hε
    refine ⟨d / 2, by positivity, fun y hy => ?_⟩
    by_cases hyc : y ≤ c
    · rw [hg y hyc, norm_zero]; exact hε.le
    · have : dist y c < d := by
        rw [Real.dist_eq, abs_of_pos (by linarith [not_le.mp hyc])]
        linarith
      have h3 : dist (g y) (g c) < ε := hdc y this
      rw [hg c le_rfl, dist_zero_right] at h3
      exact h3.le
  let m : ℝ → ℝ := fun y => min 1 (max 0 (‖g y‖ / ε - 1))
  have hm0 : ∀ y, ‖g y‖ ≤ ε → m y = 0 := fun y hy => by
    have : ‖g y‖ / ε - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hε]; exact hy
    simp only [m, max_eq_left this]
    exact min_eq_right zero_le_one
  have hmc : Continuous m := by
    have := g.continuous
    fun_prop
  let f := mulC (fun y => (m y : ℂ)) (Complex.continuous_ofReal.comp hmc) g R
    (fun y hy => by rw [hm0 y (hR y hy)]; simp)
  refine ⟨f, δ, R, hδ, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · simp [f, hm0 y (hδc y hy)]
  · simp [f, hm0 y (hR y hy)]
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun y => ?_
    have hy : (g - f).toBCF y = (1 - (m y : ℂ)) * g y := by
      show g y - (m y : ℂ) * g y = _
      ring
    rw [hy, norm_mul]
    have hm1 : m y ≤ 1 := min_le_left _ _
    have hm2 : 0 ≤ m y := le_min zero_le_one (le_max_left _ _)
    have hn : ‖(1 - (m y : ℂ))‖ = 1 - m y := by
      have : (1 - (m y : ℂ)) = ((1 - m y : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hn]
    by_cases hb : 2 * ε ≤ ‖g y‖
    · have : m y = 1 := by
        have h1 : 1 ≤ ‖g y‖ / ε - 1 := by
          have : 2 ≤ ‖g y‖ / ε := by rw [le_div_iff₀ hε]; exact hb
          linarith
        exact min_eq_left (h1.trans (le_max_right _ _))
      rw [this]; simp; positivity
    · have hgy := (not_le.mp hb).le
      have : 0 ≤ ‖g y‖ := norm_nonneg _
      nlinarith

theorem absCut : AbsCut := by
  intro H _ _ _ M Ω T F c x hyp g hg
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (norm_nonneg _))
  have hx : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨f, δ, R, hδ, h1, h2, hfg⟩ := approx c g hg (e / (2 * (‖x‖ + 1))) (by positivity)
  have hz := core F c x hyp f δ R hδ h1 h2
  have hsplit : F.Φ g x = F.Φ (g - f) x := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hz, sub_zero]
  have hb : ‖F.Φ (g - f) x‖ ≤ 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ :=
    ((F.Φ (g - f)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((F.norm_le _).trans hfg) (norm_nonneg _))
  have hc : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ ≤ e := by
    have : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ = e * (‖x‖ / (‖x‖ + 1)) := by
      field_simp
    rw [this]
    have : ‖x‖ / (‖x‖ + 1) ≤ 1 := by
      rw [div_le_one hx]; linarith
    nlinarith
  rw [hsplit]
  linarith

end Core

end GlobalTheory.CompanionTheory.FcCut
end
end

section


theorem _root_.GlobalTheory.T.positive_cone_homotopy : PositivityTheory.RgBcC.Homot := by
  first | exact @GlobalTheory.CompanionTheory.SuperHomot.homot | exact GlobalTheory.CompanionTheory.SuperHomot.homot | (intros; apply GlobalTheory.CompanionTheory.SuperHomot.homot <;> assumption)
end
