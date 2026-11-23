module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle260
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmbeddingJump

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (z : BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ[Qp] z) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * z) := by
  simp [mulVdR]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v z => simp [mulVdR, actVdR]

theorem mul_mem_DdR (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx g]

theorem tmul_mem_FilV (a : ℤ) (v : V) {z : BdR} (hz : z ∈ PD.Fil a) :
    v ⊗ₜ[Qp] z ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨z, hz⟩, by simp⟩

theorem mul_mem_FilV (a : ℤ) (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply]
    rw [mulVdR_tmul, ← Algebra.smul_def]
    exact tmul_mem_FilV PD a v ((PD.Fil a).smul_mem c z.2)

theorem mul_mul (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) c (mulVdR (K := K) (LL := LL) c' x) =
      mulVdR (K := K) (LL := LL) (c * c') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v z => simp only [mulVdR_tmul, map_mul, mul_assoc]

theorem mul_add' (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (c + c') x =
      mulVdR (K := K) (LL := LL) c x + mulVdR (K := K) (LL := LL) c' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  | tmul v z => simp only [mulVdR_tmul, map_add (f := _), add_mul, TensorProduct.tmul_add]

theorem mul_smul' (r : Qp) (c : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (r • c) x = r • mulVdR (K := K) (LL := LL) c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  | tmul v z =>
    simp only [mulVdR_tmul]
    rw [← TensorProduct.tmul_smul, ← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]

def projMap (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR) : K ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun a c => τ a • mulVdR (K := K) (LL := LL) c x)
    (fun a a' c => by rw [map_add (f := _), add_smul])
    (fun r a c => by rw [map_smul, smul_assoc])
    (fun a c c' => by rw [mul_add', smul_add])
    (fun r a c => by rw [mul_smul', smul_comm]))

theorem proj_mem (τ : K →ₐ[Qp] LL) {n : ℕ} (α β : Fin n → K)
    (h : ∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[Qp] β j = ∑ j, α j ⊗ₜ[Qp] (κ * β j)) (u : ℤ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) (hu : x ∈ FilV PD (LL := LL) (V := V) u)
    (hj : ¬ IsJumpV PD ρ τ u) :
    ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FilV PD (LL := LL) (V := V) (u + 1) := by
  have he : FildR PD ρ τ (u + 1) = FildR PD ρ τ u := not_not.1 hj
  have : ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FildR PD ρ τ u := by
    refine ⟨⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_DdR PD ρ _ hx), ?_⟩,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_FilV PD u _ hu)⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    have := congrArg (projMap τ x) (h c)

    simp only [map_sum, projMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply] at this

    simp only [map_sum, map_smul, mul_mul, Finset.smul_sum, smul_smul, ← map_mul]
    exact this.symm
  rw [← he] at this
  exact this.2

def coordMap (f : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem coordMap_mem (f : V →ₗ[Qp] Qp) (a : ℤ) {x : V ⊗[Qp] BdR}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : coordMap f x ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [coordMap, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul]
    exact ((PD.Fil a).restrictScalars Qp).smul_mem _ z.2

theorem coord_proj (τ : K →ₐ[Qp] LL) {n d : ℕ} (α β : Fin n → K) (f : V →ₗ[Qp] Qp)
    (b : Fin d → V) (y : Fin d → BdR) (s : BdR) :
    coordMap f (∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) (∑ k, b k ⊗ₜ[Qp] (y k * s))) =
      (∑ j, ∑ k, (algebraMap K BdR (β j) * algebraMap Qp BdR (f (τ (α j) • b k))) * y k) * s := by

  simp only [map_sum, mulVdR_tmul, Finset.smul_sum, TensorProduct.smul_tmul', coordMap,
  LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
  LinearMap.id_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  ring

end General

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_sum {ι : Type} (s : Finset ι) (z : ι → P.R.BdR)
    (hz : ∀ i, z i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, z i) = ∑ i ∈ s, J.θ (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (J.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hz a) _ (Submodule.sum_mem _ fun i _ => hz i), ih]

theorem theta_lin {n d : ℕ} (c : Fin n → Fin d → Om l) (y : Fin d → P.R.BdR)
    (hy : ∀ k, y k ∈ (P.PD (botExt l)).Fil 0)
    (h : ∑ j, ∑ k, algebraMap (Om l) P.R.BdR (c j k) * y k ∈ (P.PD (botExt l)).Fil 1) :
    ∑ j, ∑ k, ((c j k : Om l) : PadicComplex l) * J.θ (y k) = 0 := by
  have hm : ∀ (c : Om l) (k : Fin d), algebraMap (Om l) P.R.BdR c * y k ∈
      (P.PD (botExt l)).Fil 0 := fun c k => by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) (hy k)
    rwa [zero_add] at this
  have h3 := (J.θ_ker _ (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => hm _ k)).2 h
  rw [theta_sum J _ _ (fun j => Submodule.sum_mem _ fun k _ => hm _ k)] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [theta_sum J _ _ (fun k => hm _ k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [J.θ_mul _ (om_mem _) _ (hy k), J.θ_Om]

theorem mat_apply {n d : ℕ} (β : Fin n → Om l) (m : Fin n → Fin d → Fin d → ℚ_[l])
    (w : Fin d → PadicComplex l) (i : Fin d) :
    (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d =>
      algebraMap ℚ_[l] (PadicComplex l) (m j k i))).mulVec w i =
    ∑ k, ∑ j, ((β j * algebraMap ℚ_[l] (Om l) (m j k i) : Om l) : PadicComplex l) * w k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [UniformSpace.Completion.coe_mul]
  rfl

theorem proj_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (n : ℕ) (α β : Fin n → ↥K.1), (∀ κ : ↥K.1, ∑ j, (κ * α j) ⊗ₜ[ℚ_[l]] β j = ∑ j, α j ⊗ₜ[ℚ_[l]] (κ * β j)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∀ (u : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil 0) → ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((t ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ → ¬ IsJumpV (P.PD K) T.ρ τ u → (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (τ (α j) • b k) i))).mulVec (fun i => θ.θ (y i)) = 0 := by
  intro l _ P AI θ K LL T τ d b n α β h t ht u y hy hD hj
  obtain rfl : t = tU P := Units.ext ht
  have hF : ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((tU P ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈
      FilV (P.PD K) (LL := ↥LL.1) (V := T.V) u := by
    refine Submodule.sum_mem _ fun i _ => tmul_mem_FilV _ _ _ ?_
    have := (P.PD K).Fil_mul _ _ _ _ (hy i) ((mem_iff K u _).2 (zpow_mem θ u))
    rwa [zero_add] at this
  have h1 := proj_mem (P.PD K) T.ρ τ α β h u hD hF hj
  funext i
  have h2 := coordMap_mem (P.PD K) (b.coord i) _ h1
  rw [coord_proj, mem_iff, ← shift_iff θ, mul_left_comm, ← Units.val_mul, ← zpow_add,
    neg_add_cancel, zpow_zero, Units.val_one, mul_one] at h2
  have e : ∀ (j : Fin n) (k : Fin d), algebraMap (↥K.1) P.R.BdR (β j) *
      algebraMap ℚ_[l] P.R.BdR (b.coord i (τ (α j) • b k)) =
      algebraMap (Om l) P.R.BdR ((β j : Om l) *
        algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) := by
    intro j k
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    rfl
  simp only [e] at h2
  have h3 := theta_lin θ (fun j k => (β j : Om l) *
    algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) y (fun k => (mem_iff K 0 _).1 (hy k)) h2
  rw [Finset.sum_comm] at h3
  exact (mat_apply (fun j => (β j : Om l)) (fun j k i => b.repr (τ (α j) • b k) i) _ i).trans h3

end GlobalTheory.EmbeddingJump
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HfZero

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in
theorem nontrivial_cris : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
theorem tmul_one_inj {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have := nontrivial_cris PD
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qp B)
    (LinearMap.ker_eq_bot.2 (algebraMap Qp B).injective)
  have h1 : r 1 = 1 := by simpa using LinearMap.congr_fun hr 1
  have := congrArg (fun z => TensorProduct.rid Qp V (r.lTensor V z)) h
  simpa [h1] using this

theorem frob_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem iota_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem frob_tmul_one (v : V) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

theorem act_tmul_one (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem tmul_mem_filV (v : V) (a : ℤ) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

theorem iota_tmul_one_mem (v : V) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have : ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : BdR) := by simp [ιV]
  rw [this]
  exact tmul_mem_filV PD v 0 1 PD.one_mem

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) :=
  antitone_int_of_succ_le (filV_succ_le PD)

theorem exists_mem_filV (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem_filV PD v a b ha⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem mem_dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_ddR_iff (x : V ⊗[Qp] BdR) : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem iota_mem_ddR (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by
  rw [mem_ddR_iff]
  intro g
  rw [← iota_act, (mem_dcris_iff PD ρ x).1 hx g]

end

theorem z1f_le_b1 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], TateFilteredInvariants PD → fontCore PD → GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ → DdR PD A.ρ ≤ FilV PD (LL := LL) (V := A.V) 0 → H0V A.ρ = ⊥ → finiteCocycles PD A.ρ ≤ B1 A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ LL _ _ _ O _ _ h5 hfont hO A
    hdR hFil hH0 c hc
  obtain ⟨-, x, hx⟩ := hc
  have : Module.Finite LL ↥(Dcris PD A.ρ) := (hfont LL O hO A).1.1
  let ψ : A.V ⊗[Qp] B →ₗ[LL] A.V ⊗[Qp] B := LinearMap.id - φVB PD (LL := LL) (V := A.V)
  have hψ : ∀ z, ψ z = z - φVB PD (LL := LL) (V := A.V) z := fun z => rfl
  have hstab : ∀ z ∈ Dcris PD A.ρ, ψ z ∈ Dcris PD A.ρ := by
    intro z hz
    rw [mem_dcris_iff] at hz ⊢
    intro g
    rw [hψ, map_sub, ← frob_act, hz g]
  have hinj : Function.Injective (ψ.restrict hstab) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨z, hz⟩ h0
    have h1 : ψ z = 0 := congrArg Subtype.val h0
    rw [hψ, sub_eq_zero] at h1
    obtain ⟨v, rfl⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) z h1.symm
      (hFil (iota_mem_ddR PD A.ρ z hz))
    have hv : v ∈ H0V A.ρ := by
      simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply tmul_one_inj PD
      rw [← act_tmul_one PD A.ρ, (mem_dcris_iff PD A.ρ _).1 hz g]
    rw [hH0, Submodule.mem_bot] at hv
    subst hv
    exact Subtype.ext (TensorProduct.zero_tmul _ _)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hy : ψ x ∈ Dcris PD A.ρ := by
    rw [mem_dcris_iff]
    intro g
    have h1 := frob_tmul_one PD (LL := LL) (c g)
    rw [hx g, map_sub, frob_act] at h1
    rw [hψ, map_sub, sub_eq_sub_iff_sub_eq_sub, h1]
  obtain ⟨⟨x', hx'⟩, hxx⟩ := hsurj ⟨ψ x, hy⟩
  have h2 : ψ x' = ψ x := congrArg Subtype.val hxx
  have hfix : φVB PD (LL := LL) (V := A.V) (x - x') = x - x' := by
    rw [hψ, hψ, sub_eq_sub_iff_sub_eq_sub] at h2
    rw [map_sub, ← neg_sub x' x, h2, neg_sub]
  obtain ⟨a, ha⟩ := exists_mem_filV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)
  obtain ⟨w, ⟨hw, -⟩, hw'⟩ := h5 LL O hO A hdR a 0 _ ha (fun g => by
    rw [← iota_act, ← map_sub, ← hx g]
    exact iota_tmul_one_mem PD (c g))
  have hF : ιV PD (LL := LL) (V := A.V) (x - x') ∈ FilV PD (LL := LL) (V := A.V) 0 := by
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hw' (hFil hw))
      (hFil (iota_mem_ddR PD A.ρ x' hx'))
    rwa [sub_add_cancel, ← map_sub] at h3
  obtain ⟨v, hv⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) _ hfix hF
  refine ⟨v, funext fun g => ?_⟩
  change A.ρ g v - v = c g
  apply tmul_one_inj PD
  rw [hx g, TensorProduct.sub_tmul, ← act_tmul_one PD A.ρ, ← hv, map_sub,
    (mem_dcris_iff PD A.ρ _).1 hx' g]
  abel

end GlobalTheory.HfZero
end

section

open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

def unitBallSubring (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] : Subring E where
  carrier := {t | ‖t‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem norm_det_one_add_smul (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ‖(1 + ϖ • x).det‖ = 1 := by
  set O := unitBallSubring E
  let y : Matrix (Fin n) (Fin n) O := fun i j => ⟨x i j, hx i j⟩
  let w : O := ⟨ϖ, hϖ.le⟩
  have hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x := by
    rw [map_add (f := _), map_one]
    congr 1
  have hdet : (1 + ϖ • x).det = ((1 + w • y).det : E) := by
    rw [← hmap, ← RingHom.map_det]; rfl
  have hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1 := by
    rw [RingHom.map_det, map_add (f := _), map_one]
    have : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0 := by
      ext i j
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rw [this, add_zero, Matrix.det_one]
  have hmem : (1 + w • y).det - 1 ∈ Ideal.span {w} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ := by
    have := congrArg Subtype.val hc
    simpa [w] using this.symm
  have hlt : ‖(1 + ϖ • x).det - 1‖ < 1 := by
    rw [hdet, hc', norm_mul]
    calc ‖(c : E)‖ * ‖ϖ‖ ≤ 1 * ‖ϖ‖ := mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hϖ
  have key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1) := by ring
  rw [key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]
  simp [hlt.le]

end GlobalTheory.UnitDiscAlg
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal : ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_corner_separable_charpoly | exact GlobalTheory.SpanRing.exists_corner_separable_charpoly | (intros; apply GlobalTheory.SpanRing.exists_corner_separable_charpoly <;> assumption)
end
