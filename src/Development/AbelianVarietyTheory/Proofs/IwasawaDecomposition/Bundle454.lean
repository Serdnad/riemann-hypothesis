module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle435
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle405
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle437
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosets
public import Formalism.LocalToGlobal.Columns.Bundle015
public import Formalism.LocalToGlobal.Columns.Bundle018
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Formalism.LocalToGlobal.Columns.TwQLev
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle423
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle439
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftFin

variable {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
  {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)}

theorem word_ker (hκ : IsKerSys θ V W κ) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (f : M) : ∃ f', ∀ h, word θ V l (fun g => κ f g h) = fun g => κ f' g h := by
  induction l with
  | nil => exact ⟨f, fun _ => rfl⟩
  | cons p l ih =>
    obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨f'', e'⟩ := hκ.derV p.1 p.2 (hl p List.mem_cons_self) f'
    refine ⟨f'', fun h => ?_⟩
    change Rder θ V p.1 p.2 (word θ V l fun g => κ f g h) = _
    rw [e h]
    funext g
    exact (e' g h).deriv

theorem isMod_ker (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (f : M) (h : GA D W) : IsMod θ V fun g => κ f g h := by
  have hc : ∀ f, Continuous fun g => κ f g h := fun f => (hκ.cont f).comp (Continuous.prodMk_left h)
  refine ⟨GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ V (Set.range fun f g => κ f g h) ?_ ?_ _ ⟨f, rfl⟩, fun γ hγ g => ?_, fun l hl => ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact hc f
  · rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hκ.derV τ X hX f
    exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
  · simpa using hκ.left f γ hγ 1 (one_mem _) g h
  · obtain ⟨f', e⟩ := word_ker hκ l hl f
    obtain ⟨N, hN⟩ := hκ.growth
    obtain ⟨C, hC⟩ := hN f'
    rw [e h]
    refine ⟨hc f', N, C * (height θ W h : ℝ) ^ N, fun g => (hC g h).trans_eq ?_⟩
    ring


variable (κ) in
def lift (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (f : M) (F : GA D V → ℂ) : GA D W → ℂ :=
  fun h => ∫ g in 𝓕, κ f g h * F g ∂μ

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem lift_add_left (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (f f' : M) : lift κ μ 𝓕 (f + f') F = lift κ μ 𝓕 f F + lift κ μ 𝓕 f' F := by
  have I := (GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1
  funext h
  simp only [lift, map_add (f := _), Pi.add_apply, add_mul]
  exact integral_add (I f h) (I f' h)

theorem lift_add_right (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {F F' : GA D V → ℂ}
    (hF : F ∈ Decay θ V) (hF' : F' ∈ Decay θ V) (f : M) :
    lift κ μ 𝓕 f (F + F') = lift κ μ 𝓕 f F + lift κ μ 𝓕 f F' := by
  funext h
  simp only [lift, Pi.add_apply, mul_add]
  exact integral_add ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).1 f h)
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F' hF').1 f h)

theorem lift_smul_left (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 (c • f) F = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem lift_smul_right (c : ℂ) (F : GA D V → ℂ) (f : M) : lift κ μ 𝓕 f (c • F) = c • lift κ μ 𝓕 f F := by
  funext h
  simp only [lift, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _


variable (θ κ μ 𝓕) in
def Compat (T : (GA D W → ℂ) → (GA D W → ℂ)) : Prop :=
  ∀ f, ∃ f', (∀ g, T (κ f g) = κ f' g) ∧ ∀ F ∈ Decay θ V, T (lift κ μ 𝓕 f F) = lift κ μ 𝓕 f' F

theorem compat_id : Compat θ κ μ 𝓕 fun φ => φ := fun f => ⟨f, fun _ => rfl, fun _ _ => rfl⟩

theorem Compat.comp {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S (T φ) := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  obtain ⟨f'', c, d⟩ := hS f'
  exact ⟨f'', fun g => by simp only [a, c], fun F hF => by simp only [b F hF, d F hF]⟩

theorem Compat.add (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕)
    {S T : (GA D W → ℂ) → (GA D W → ℂ)} (hS : Compat θ κ μ 𝓕 S) (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => S φ + T φ := fun f => by
  obtain ⟨f', a, b⟩ := hS f
  obtain ⟨f'', c, d⟩ := hT f
  exact ⟨f' + f'', fun g => by simp only [a, c, map_add (f := _), Pi.add_apply],
    fun F hF => by simp only [b F hF, d F hF, lift_add_left hθ hκ hq hF]⟩

theorem Compat.smul (c : ℂ) {T : (GA D W → ℂ) → (GA D W → ℂ)} (hT : Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => c • T φ := fun f => by
  obtain ⟨f', a, b⟩ := hT f
  exact ⟨c • f', fun g => by simp only [a, map_smul, Pi.smul_apply], fun F hF => by simp only [b F hF, lift_smul_left]⟩

theorem compat_sum (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {ι : Type} (s : Finset ι)
    (T : ι → (GA D W → ℂ) → (GA D W → ℂ)) (hT : ∀ i, Compat θ κ μ 𝓕 (T i)) :
    Compat θ κ μ 𝓕 fun φ => ∑ i ∈ s, T i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (compat_id (θ := θ) (κ := κ) (μ := μ) (𝓕 := 𝓕)).smul 0
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hT i).add hθ hκ hq ih

theorem compat_foldr (l : List ((GA D W → ℂ) → (GA D W → ℂ))) (hl : ∀ T ∈ l, Compat θ κ μ 𝓕 T) :
    Compat θ κ μ 𝓕 fun φ => l.foldr (fun T acc => T acc) φ := by
  induction l with
  | nil => exact compat_id
  | cons T l ih => exact (hl T List.mem_cons_self).comp (ih fun S hS => hl S (List.mem_cons_of_mem _ hS))

theorem compat_Rder (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {X : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hX : X ∈ lieAt W τ) : Compat θ κ μ 𝓕 (Rder θ W τ X) := fun f => by
  obtain ⟨f', e⟩ := hκ.derW τ X hX f
  exact ⟨f', fun g => funext fun h => (e g h).deriv, fun F hF => funext fun h =>
    ((GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hF).2.2.2 τ X hX f f' e h).deriv⟩

theorem compat_gelf (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) (τ : D.what₂.Tau) (k : ℕ) :
    Compat θ κ μ 𝓕 (gelf θ W τ k) := by
  refine compat_sum hθ hκ hq Finset.univ _ fun idx : Fin (k + 1) → Fin W.rank =>
    compat_foldr (List.ofFn fun a : Fin (k + 1) => RderC θ W τ (Matrix.single (idx a) (idx (a + 1)) 1)) fun T hT => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem W τ (Matrix.single (idx a) (idx (a + 1)) 1)
  exact (compat_Rder hθ hκ hq h1).add hθ hκ hq ((compat_Rder hθ hκ hq h2).smul Complex.I)

theorem lift_adjoin (hθ : IsInfFam θ) (hκ : IsKerSys θ V W κ) (hq : IsQuot V μ 𝓕) {τ : D.what₂.Tau}
    {a : ℕ → Module.End ℂ M} (ha : ∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h)
    {Z : Submodule ℂ (GA D V → ℂ)} (hZ : ∀ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) {x : Module.End ℂ M}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ f, ∀ F ∈ Decay θ V ⊓ Z, ∃ F' ∈ Decay θ V ⊓ Z, lift κ μ 𝓕 (x f) F = lift κ μ 𝓕 f F' := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    intro f F hF
    obtain ⟨F', hF', e⟩ := GlobalTheory.T.gelfand_operator_adjoint_decaying D θ hθ V μ 𝓕 hq τ Z hZ k F hF
    refine ⟨F', hF', funext fun h => ?_⟩
    have := e _ (isMod_ker hθ hκ f h)
    rw [ha] at this
    exact this
  | algebraMap r =>
    intro f F hF
    exact ⟨r • F, Submodule.smul_mem _ r hF, by rw [Module.algebraMap_end_apply, lift_smul_left, lift_smul_right]⟩
  | add x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx f F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F hF
    exact ⟨F₁ + F₂, add_mem h₁ h₂, by
      rw [LinearMap.add_apply, lift_add_left hθ hκ hq hF.1, lift_add_right hθ hκ hq h₁.1 h₂.1, e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    intro f F hF
    obtain ⟨F₁, h₁, e₁⟩ := hx (y f) F hF
    obtain ⟨F₂, h₂, e₂⟩ := hy f F₁ h₁
    exact ⟨F₂, h₂, by rw [Module.End.mul_apply, e₁, e₂]⟩

theorem lift_zfin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  rintro D θ hθ V W M _ _ κ hκ μ 𝓕 hq F hF ⟨Z, hfin, hFZ, hZ⟩ f
  let L : ↥(Decay θ V ⊓ Z) →ₗ[ℂ] (GA D W → ℂ) :=
    { toFun := fun F' => lift κ μ 𝓕 f F'.1
      map_add' := fun F₁ F₂ => lift_add_right hθ hκ hq F₁.2.1 F₂.2.1 f
      map_smul' := fun c F' => lift_smul_right c F'.1 f }
  refine ⟨LinearMap.range L, inferInstance, ⟨⟨F, hF, hFZ⟩, rfl⟩, ?_⟩
  rintro τ k _ ⟨F₁, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hκ.cap τ
  obtain ⟨f', e, e'⟩ := compat_gelf hθ hκ hq τ k f
  obtain ⟨F₂, h₂, e₂⟩ := lift_adjoin hθ hκ hq ha (hZ τ) (hab ▸ Algebra.subset_adjoin ⟨k, rfl⟩ : b k ∈ _) f F₁.1 F₁.2
  refine ⟨⟨F₂, h₂⟩, ?_⟩
  change lift κ μ 𝓕 f F₂ = gelf θ W τ k (lift κ μ 𝓕 f F₁.1)
  rw [e' _ F₁.2.1, ← e₂]
  funext h
  simp only [lift, ← e, hb]

end GlobalTheory.Mem.LiftFin

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem inv_mul_mem_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (a b : ∀ i, G i)
    (h : ∀ i, (a i)⁻¹ * b i ∈ H i) : a⁻¹ * b ∈ Subgroup.pi Set.univ H := fun i _ => h i

theorem reindex_finCongr_rfl {κ : Type} [CommRing κ] {a : ℕ} (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ (finCongr (rfl : a = a))).toMonoidHom y = y := by
  apply Units.ext
  ext i j
  rfl

theorem coarse_eq_blkOf {a r t m : ℕ} (hn : a = r + m * t) (i : Fin a) :
    Formalism.L2.Col.coarse r (List.replicate m t) i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
        omega
      · exact h0
    rw [Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]

theorem coarseBlockIndex_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem reindex_inv_mul_diag_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ *
        Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HK n κ r (List.replicate m t) := by
  subst h
  rw [reindex_finCongr_rfl]
  have hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := by
    intro i j hij
    apply hy
    have hij' : Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val := hij
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn] at hij'
    exact hij'
  have hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := Formalism.L2.DIV.blockTri_blkOf_le r t hy
  refine Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy')
    (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩
  let Y : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate m t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Dd = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val]
    ext i' j'
    exact Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)
  have hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Y = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]
    rfl
  have h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) (Y⁻¹ * Dd) = 1 := by
    rw [map_mul, map_inv, hD, hY, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1
  simp only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2
  have h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j =
      (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := h2
  rw [h3]
  simp only [Matrix.one_apply, Fin.ext_iff]

theorem reindex_inv_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ * 1 ∈ Formalism.L2.Col.blockUT n κ r [b] := by
  subst h
  rw [reindex_finCongr_rfl, mul_one]
  refine Subgroup.inv_mem _ ?_
  intro i j hij
  apply hy
  have hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val := hij
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn] at hij'
  exact hij'

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd



theorem inv_redG_mul_g0Hat_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  intro X px I U L eG hI hL hG t q hz
  apply inv_mul_mem_pi
  intro w
  show _ ∈ (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H
  rw [redG_ptE X I L hL t q hz w]
  have hQ := RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q
  by_cases hw : w.1 ∈ (X.B.primes px).vGs
  · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]
    have hPg : w.1 ∈ L.Pg := by rw [hL.Pg]; exact hw
    have hPg' : w.1 ∈ (L.datXt t).Pg := hPg
    have hy := Formalism.L2.DIV.parLev_g hQ hPg'
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w =
        Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_X' X.B.R) (g ⟨w.1, hw⟩) := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]
      rfl
    rw [hg0]
    have hgg : ∀ z, (eG.symm z) ⟨w.1, hw⟩ = z ⟨w.1, hPg⟩ := fun z => by
      rw [← hG (eG.symm z) w.1 hw hPg, MulEquiv.apply_symm_apply]
    have key := reindex_inv_mul_diag_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr
      (Formalism.L2.Col.r_le_X' X.B.R) _ hy
    convert key using 3 <;> first | rfl | exact heq_of_eq (hgg _) | exact hgg _
  · have hwQ : w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      classical
      exact (Finset.mem_union.1 w.2).resolve_left hw
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      simp only [ColIn.Q, tup_ixOf]
    have hQt : w.1 ∈ L.Q t := by
      rw [hL.Q t, e]
      exact hwQ
    have hQt' : w.1 ∈ (L.datXt t).Q := hQt
    have hy := Formalism.L2.DIV.parLev_q hQ hQt'
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = 1 := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]
    rw [hg0]
    exact reindex_inv_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hy

end GlobalTheory.Mem.R3.RowDeco
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_twistPrime_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.cqOf_empty_or_coset | exact GlobalTheory.Mem.Col2.ChEx.cqOf_empty_or_coset | (intros; apply GlobalTheory.Mem.Col2.ChEx.cqOf_empty_or_coset <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepPoint_determined_by_latticeInvariants : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | exact GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_stepPoint_given_reductions_cosets : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (p : ChPt (R := R) sel mu u j), ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r' = GlobalTheory.Mem.Col2.ChEx.cqOf r := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq | exact GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq | (intros; apply GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.openLevel_cutByCosetStabiliser : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q), ThetaOpen Θ → ∀ (C : ∀ P : Q, Set (Sp E n)), (∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) → ThetaOpen (GlobalTheory.Mem.Col2.ChEx.cutQ Θ C) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | exact GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ | (intros; apply GlobalTheory.Mem.Col2.ChEx.thetaOpen_cutQ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartClassStabiliser_rationalParts : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → ∀ (c : (stR Λ Θ p₀ pref).Cl) (b : β), c.1 = b → ∀ (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar (rp Λ Θ p₀ pref c) = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq (rp Λ Θ p₀ pref c) = D → ∀ (γ : GL (Fin n) X.E), (γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(GlobalTheory.Mem.Col2.ChEx.cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧ g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.stM_range_tw | exact GlobalTheory.Mem.Col2.ChEx.stM_range_tw | (intros; apply GlobalTheory.Mem.Col2.ChEx.stM_range_tw <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartClasses_bijective_orbits_framedLattices : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.clsF_bij | exact GlobalTheory.Mem.Col2.ChEx.clsF_bij | (intros; apply GlobalTheory.Mem.Col2.ChEx.clsF_bij <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartLevel_iff_frames_onPoints : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.lev_iff_frames | exact GlobalTheory.Mem.Col2.ChEx.lev_iff_frames | (intros; apply GlobalTheory.Mem.Col2.ChEx.lev_iff_frames <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartCharacter_frames_onPoints : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chr_frames | exact GlobalTheory.Mem.Col2.ChEx.chr_frames | (intros; apply GlobalTheory.Mem.Col2.ChEx.chr_frames <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.piKop_fix | exact GlobalTheory.HeightCounting.FormsStep.piKop_fix | (intros; apply GlobalTheory.HeightCounting.FormsStep.piKop_fix <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | exact GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero <;> assumption)
end
