module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem unif_ne_zero {ϖ : Fv F v} (hϖ : IsUnif v ϖ) : ϖ ≠ 0 := by
  rintro rfl
  unfold IsUnif at hϖ
  rw [map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omAt_compl_zero {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    omAt σ J ψ v T {X | gramR (Fv F v) σ J X = T}ᶜ = 0 := by
  unfold omAt
  split_ifs with hT
  · unfold omFam
    split_ifs with hf
    · have h1 := (hf.choose_spec).1 ⟨T, hT⟩
      refine measure_mono_null (fun X hX => ?_) h1
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hX
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, not_and]
      intro h; exact absurd h hX
    · simp
  · simp

theorem smul_mem_LamT {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : Y ∈ LamT v Λ a) : k • Y ∈ LamT v Λ a := by
  intro i
  exact (hk (Y i)).1 (hY i)

theorem qv_pos : 0 < qv v := by
  unfold qv
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem absV_dV_pos : 0 < absV v (dV v) := by
  have hd : dV v ≠ 0 := by
    unfold dV; split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  unfold absV
  rw [dite_eq_right (by simpa using hd)]
  exact zpow_pos (qv_pos v) _

theorem omLocU_of (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  intro hS hL hSD hUn ha hP hdet
  have hG : GoodY σ J ψ v Λ a Y := ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩
  obtain ⟨ϖ, hϖ⟩ := hU
  obtain ⟨hW, hH⟩ := hSd hS
  set T := gramR (Fv F v) σ J Y with hTdef
  set ω := omAt σ J ψ v T with hω
  set O := {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} with hO

  have hYL : Y ∈ LamT v Λ a := hP.1
  have hsub : O ⊆ LamT v Λ a := by
    rintro X ⟨k, hk, rfl⟩; exact smul_mem_LamT σ J v Λ k hk Y hYL
  have hsup : LamT v Λ a ⊆ O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ := by
    intro X hX
    by_cases hg : gramR (Fv F v) σ J X = T
    · exact Or.inl (h1 hG X hX hg)
    · exact Or.inr hg
  have hEq : ω O = ω (LamT v Λ a) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (LamT v Λ a) ≤ ω (O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {X | gramR (Fv F v) σ J X = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero σ J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, h2 hG (hOm hS).1 ϖ hϖ, h3 hG hW ϖ hϖ, h4 hS hL hSD hUn hW, h5 hS hUn hH ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((n : ℝ) * a) / absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEta
  have : (0 : ℝ) < qv v ^ (-((a : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct

theorem unifEx_holds {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    UnifEx v := by
  refine ⟨PI.VolStabSW.unifV v, ?_⟩
  unfold IsUnif
  rw [PI.VolStabSW.unifV_val]
  rfl

theorem unif_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : Fv F v)
    (hϖ : IsUnif v ϖ) : ϖ ≠ 0 ∧ Tendsto (fun k : ℕ => ϖ ^ k) atTop (𝓝 0) ∧
      ϖ ∈ v.adicCompletionIntegers F := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h1 : Valued.v ϖ < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

section Sub

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem oEv_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.add_mem _ hx hy

theorem oEv_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.zero_mem _

theorem oEv_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.neg_mem _ hx

def lamS (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def hermOE (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := by
    intro x y hx hy i j
    exact oEv_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oEv_zero v
  neg_mem' := by
    intro x hx i j
    exact oEv_neg v (hx i j)

def lamN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (TupV (E := E) v n a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (lamS v Λ a)

def hN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (hermOE σ v a)

def FibU' (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (LamT v Λ a) =
      dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def LamOC (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsOpen (LamT v Λ a) ∧ IsCompact (LamT v Λ a)

def HermOC (a : ℕ) : Prop :=
  IsOpen (hermOE σ v a : Set (HermR (Fv F v) σ a)) ∧ IsCompact (hermOE σ v a : Set (HermR (Fv F v) σ a))

def FibHens (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j),
    ∀ y ∈ LamT v Λ a, PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
        PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y ∈ hN σ v ϖ a 0 →
      ∃ D : TupV (E := E) v n a →+ HermR (Fv F v) σ a,
        (∀ k, (lamN v Λ ϖ a k).map D = hN σ v ϖ a k) ∧
        ∀ k, ∀ Z ∈ lamN v Λ ϖ a 0, ∀ W ∈ lamN v Λ ϖ a k,
          PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z + W) -
            PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈ hN σ v ϖ a (k + 1)

end Sub

end PI.OmLocU
end
end
