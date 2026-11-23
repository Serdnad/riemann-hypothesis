module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

namespace Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def crd (V : HSp D) : (Fin V.rank → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm

def l0s (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.comap ((crd V).toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_self_dual_lattice_set (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ l0s V ↔ x ∈ L0c D V := by
  simp [l0s, crd, L0c, Module.Basis.equivFun_symm_apply]

theorem hT_crd (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (crd V x) (crd V y) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by

  simp only [crd, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
  LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem self_dual_lattice_is_self_dual (V : HSp D) : Datum.IsSelfDualC V (l0s V) := by
  refine ⟨?_, fun y => ?_⟩
  · have hL := V.standardTuple_isLattice
    let f : V.V ≃ₗ[D.host.E] (Fin V.rank → D.host.E) := (crd V).symm
    have heq : l0s V = V.L0.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext x
      simp only [l0s, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, f]
      constructor
      · intro hx; exact ⟨crd V x, hx, by simp⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [heq]
    refine ⟨hL.fg.map _, ?_⟩
    have hc : (↑(Submodule.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) V.L0) : Set (Fin V.rank → D.host.E)) =
        f.toLinearMap '' (V.L0 : Set V.V) := by ext; simp
    rw [hc]
    intro s hs hi
    have hi' : LinearIndependent (𝓞 D.host.E) (fun x : s => f.symm x) := by
      simpa only [Function.comp_def, id_eq, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] using
        hi.map' (f.symm.toLinearMap.restrictScalars (𝓞 D.host.E))
          (LinearMap.ker_eq_bot.mpr f.symm.injective)
    have hm : ∀ x : s, f.symm x ∈ V.L0 := by
      intro x
      obtain ⟨z, hz, hze⟩ := hs x.property
      change f z = x at hze
      rw [← hze, LinearEquiv.symm_apply_apply]
      exact hz
    let _ := hL
    have hk := Submodule.IsLattice.linearIndependent D.host.E V.L0 hm hi'
    simpa only [LinearIndepOn, Function.comp_def, id_eq, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      hk.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr f.injective)
  · have key : ∀ b : 𝓞 D.host.E, LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E 1 b = (b : D.host.E) := fun b => by
      simp [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    have hU := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
    constructor
    · intro hy x hx
      have hy' : crd V y ∈ Formalism.E.hdual V.hT V.L0 := by rw [hU]; exact hy
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'
      obtain ⟨b, hb⟩ := hy' (crd V x) hx
      exact ⟨b, by rw [← hT_crd, ← hb, key]⟩
    · intro h
      show crd V y ∈ V.L0
      rw [← hU]
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro z hz
      obtain ⟨b, hb⟩ := h ((crd V).symm z) (by simpa [l0s] using hz)
      refine ⟨b, ?_⟩
      rw [show z = crd V ((crd V).symm z) by simp, hT_crd, key]
      exact hb

end Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  rw [actO_eq, actO_eq, actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_eq, Matrix.mul_zero, Matrix.zero_mul]
  | succ k ih => rw [succ_nsmul, actO_add, ih, succ_nsmul]

theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx

def actPull {S T : HSp D} (p : GA D S × GA D T) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun t => Φ (actO S T p.1⁻¹ p.2⁻¹ t)

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct




namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε


theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl



section Sym

variable (S T : HSp D)

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add (f := _), ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this


end Phi

section Lat

variable (S T : HSp D)

variable {S T}

end Lat

end Formalism.IndefR.Fin.VacEx
end
end
