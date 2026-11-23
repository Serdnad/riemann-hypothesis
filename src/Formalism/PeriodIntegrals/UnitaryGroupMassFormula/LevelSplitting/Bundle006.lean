module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnipotentRadicalActionFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ

theorem modulus_all_extensions : PI.LevelKSplit.W.CD.ModVAll :=
  modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds

end PI.LevelKSplit.W.MVA
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def HeisP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ sH : (Fin r → Wp (Af F) σ J P) → HA (Af F) σ J,
    Continuous sH ∧ Continuous (yH (Af F) σ J P) ∧
    (∀ y, sH y ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, ∃ y : Fin r → Wp (Af F) σ J P,
      (∀ a, (y a : Fin M → Af F ⊗[F] E) = yH (Af F) σ J P n a) ∧ (sH y)⁻¹ * n ∈ Zsub (Af F) σ J P) ∧
    (∀ y, ∀ z ∈ Zsub (Af F) σ J P, ∀ a, yH (Af F) σ J P (sH y * z) a = y a) ∧
    Zsub (Af F) σ J P ≤ LevelUnipotentSubgroup (Af F) σ J P ∧
    (∀ z ∈ Zsub (Af F) σ J P, ∀ n ∈ LevelUnipotentSubgroup (Af F) σ J P, z * n = n * z) ∧
    (∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, n * z * n⁻¹ ∈ Zsub (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ y, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧ h * sH y * h⁻¹ = sH y') ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ z ∈ Zsub (Af F) σ J P, h * z * h⁻¹ = z)

def LevP : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A : Subgroup (HA (Af F) σ J)) (Lev : HA (Af F) σ J → HA (Af F) σ J),
    A ≤ Nsub (Af F) σ J P ∧ IsClosed (A : Set (HA (Af F) σ J)) ∧ Continuous Lev ∧
    (∀ n ∈ Nsub (Af F) σ J P, Lev n ∈ A ∧ (Lev n)⁻¹ * n ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ u ∈ A, u ∈ LevelUnipotentSubgroup (Af F) σ J P → u = 1) ∧
    (∀ n ∈ Nsub (Af F) σ J P, ∀ m ∈ LevelUnipotentSubgroup (Af F) σ J P, n * m * n⁻¹ ∈ LevelUnipotentSubgroup (Af F) σ J P) ∧
    (∀ h ∈ Hsub (Af F) σ J P, ∀ u ∈ A, h * u = u * h)

end Ext

def HeisPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => HeisP F E σ M J
def LevPAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => LevP F E σ M J

end PI.LevelKSplit.W.NC
end
end

section

noncomputable section

namespace PI.LevelKSplit.W.NCH

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)

theorem continuous_pWpR : Continuous (PI.LevelKSplit.W.NC.pWp R σ J P) := by
  show Continuous fun x => PI.LevelKSplit.W.NC.pWp R σ J P x
  unfold PI.LevelKSplit.W.NC.pWp
  refine (continuous_id.sub ?_).sub ?_ <;>
  refine continuous_finsetSum _ fun a _ => ?_ <;>
  exact (PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := continuous_const) (hv := continuous_id)).smul continuous_const

theorem continuous_yH : Continuous (PI.LevelKSplit.W.NC.yH R σ J P) := by
  refine continuous_pi fun a => ?_
  exact (continuous_pWpR P).comp (PI.VolSemiDirect.W.Md.continuous_linear_action _ σ J (hg := continuous_id) (hv := continuous_const))

theorem continuous_sL_apply (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by
  have hh : ∀ {u w : X → Fin M → R ⊗[F] E}, Continuous u → Continuous w →
      Continuous fun x => (PI.VolSemiDirect.W.datR R σ J P T).h (u x) (w x) :=
    fun hu hw => PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := hu) (hv := hw)
  simp only [sL, uv, cf, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply, PI.VolSemiDirect.W.PG.Dat.hL,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine (continuous_const.add (continuous_finsetSum _ fun a _ => ?_)).sub
    (continuous_finsetSum _ fun b _ => ?_)
  · exact (hh continuous_const continuous_const).smul (((continuous_apply a).comp hy).add
      (continuous_finsetSum _ fun b _ => ((continuous_const.mul
        (hh ((continuous_apply b).comp hy) ((continuous_apply a).comp hy))).neg).smul continuous_const))
  · exact (hh ((continuous_apply b).comp hy) continuous_const).smul continuous_const

theorem continuous_sLmat (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) :
    Continuous fun x => LinearMap.toMatrix' (sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (continuous_sL_apply P T half hy _)

end Cont

end PI.LevelKSplit.W.NCH
end
end
