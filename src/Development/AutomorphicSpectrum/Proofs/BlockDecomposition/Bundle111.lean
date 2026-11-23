module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle098
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle093
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle094
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem _root_.GlobalTheory.T.block_embedding_GL_inverse : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d → ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb | (intros; apply GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.exists_gl_blkEmb <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.denominator_norm_quadratic_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ x : F, Ideal.absNorm (den E (algebraMap F E x)) = Ideal.absNorm (den F x) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.lam_is_lattice : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Matrix (Fin m) (Fin m) K), IsLat (lam c) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.mem_lattice_of_dual_pairing : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K, (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) → a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix


theorem _root_.GlobalTheory.T.denominator_index_bound : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)), 𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c → (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) → ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) → Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx <;> assumption)
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Alg

variable {k : Type} [Field k]

theorem mul_inv_mem_Q_of_rowQ_eq (n : ℕ) (a b : Mir k (n + 1)) (h : rowQ k n a = rowQ k n b) :
    a * b⁻¹ ∈ Q k n := by
  show GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹) ∈ GlobalTheory.BZMir.Mir k n
  have hab : Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) a) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) b) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [GlobalTheory.BZMir.vecMul_eLast, GlobalTheory.BZMir.vecMul_eLast]
    funext j
    exact congrFun h j
  rw [GlobalTheory.BZMir.mem_Mir_iff, ← GlobalTheory.BZMir.vecMul_eLast k n
    (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
    map_mul, map_inv, Units.val_mul, ← Matrix.vecMul_vecMul, hab, Matrix.vecMul_vecMul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def rowMat (n : ℕ) (r : Fin (n + 1) → k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k :=
  (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k).updateRow (Fin.castSucc (Fin.last n))
    (Fin.lastCases (motive := fun _ => k) 0 r)

theorem rowMat_single (n : ℕ) : rowMat n (Pi.single (Fin.last n) (1 : k)) = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp [Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      by_cases hj : j = Fin.last n
      · subst hj
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  · rfl

def rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) : Mir k (n + 1) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMat n r) h, by
    rw [mem_Mir_iff]
    show rowMat n r (Fin.last (n + 1)) = eLast k (n + 1)
    rw [rowMat, updateRow_ne (Fin.castSucc_ne_last _).symm]
    funext j
    simp only [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, eq_comm]⟩

theorem rowQ_rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    rowQ k n (rowEl n r h) = r := by
  funext j
  show GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = r j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_self, Fin.lastCases_castSucc]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_rowMat (n : ℕ) : Continuous (rowMat (k := k) n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat]
  by_cases hi : i = Fin.castSucc (Fin.last n)
  · subst hi
    simp only [Matrix.updateRow_self]
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      exact continuous_const
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact continuous_apply j
  · simp only [Matrix.updateRow_ne hi]
    exact continuous_const

theorem continuous_rowEl (n : ℕ) :
    Continuous fun r : {r : Fin (n + 1) → k // (rowMat n r).det ≠ 0} => rowEl n r.1 r.2 := by
  have hM : Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
      GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1 :=
    (GlobalTheory.CompanionTheory.BZPhiPhi.continuous_rowMat n).comp continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  refine ⟨hM, ?_⟩
  simp only [Function.comp_apply, Matrix.coe_units_inv]
  show Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
    (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1)⁻¹
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun r => r.2).smul hM.matrix_adjugate

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den

variable {F : Type} [Field F] [NumberField F]

theorem exists_pow_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v)
    (ha : Valued.v a < 1) (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m : ℕ, ∀ s ∈ K, Valued.v (a ^ m * s) ≤ 1 := by
  have h1 : IsOpen {s : Fv F v | Valued.v s < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    have hy' : Valued.v (y - x) < 1 := by simpa using hy
    have h := Valuation.map_add_lt Valued.v hy' hx
    simpa using h
  have h2 : Tendsto (fun m : ℕ => a ^ m) atTop (𝓝 0) := Valued.tendsto_zero_pow_of_v_lt_one ha
  have hUo : ∀ m : ℕ, IsOpen {s : Fv F v | Valued.v (a ^ m * s) < 1} := fun m =>
    (continuous_const.mul continuous_id).isOpen_preimage _ h1
  have hcover : ∀ s : Fv F v, ∃ m : ℕ, Valued.v (a ^ m * s) < 1 := by
    intro s
    have h0 : Tendsto (fun m : ℕ => a ^ m * s) atTop (𝓝 0) := by
      simpa using h2.mul_const s
    have hn : {y : Fv F v | Valued.v y < 1} ∈ 𝓝 (0 : Fv F v) := h1.mem_nhds (by simp)
    exact (h0.eventually hn).exists
  have hmono : Monotone fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1} := by
    intro m m' hmm' s hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm'
    show Valued.v (a ^ (m + d) * s) < 1
    rw [show a ^ (m + d) * s = a ^ d * (a ^ m * s) by ring, Valuation.map_mul, map_pow]
    calc Valued.v a ^ d * Valued.v (a ^ m * s) ≤ 1 * Valued.v (a ^ m * s) := by
          gcongr
          first
            | exact pow_le_one₀ zero_le ha.le
            | exact pow_le_one₀ zero_le' ha.le
      _ = Valued.v (a ^ m * s) := one_mul _
      _ < 1 := hs
  obtain ⟨m, hm⟩ := hK.elim_directed_cover (fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1}) hUo
    (fun s _ => Set.mem_iUnion.mpr (hcover s)) hmono.directed_le
  exact ⟨m, fun s hs => le_of_lt (hm hs)⟩

theorem exists_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ v.valuation F (p : F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h : (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) = ((Ideal.absNorm v.asIdeal : ℕ) : F) := by simp
  rw [← h]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hm

theorem val_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : v.valuation F (n : F) ≤ 1 := by
  have h : ((n : 𝓞 F) : F) = (n : F) := by simp
  rw [← h]
  exact HeightOneSpectrum.valuation_le_one v _

end GlobalTheory.CompanionTheory.Mass.MeanV.Den

theorem GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator :
    ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  intro F _ _ T K hK
  have h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
    intro v x
    show Valued.v ((x : v.adicCompletion F)) = v.valuation F x
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' x
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) x
  have h4 : ∀ x : F, (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1) → ∃ y : 𝓞 F, (y : F) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := x) (h := hx)
    exact ⟨y, hy⟩
  have hpl : ∀ (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ), v.valuation F ((n : F) ^ k) ≤ 1 := by
    intro v n k
    rw [← Nat.cast_pow]
    exact Den.val_nat_le_one v _
  choose p hp0 hp1 using fun v : HeightOneSpectrum (𝓞 F) => Den.exists_nat_lt_one v
  have hm : ∀ v ∈ T, ∃ m : ℕ, ∀ s ∈ K v, Valued.v (algebraMap F (Fv F v) (p v : F) ^ m * s) ≤ 1 :=
    fun v hv => Den.exists_pow_mul_le_one v _ (by rw [h3]; exact hp1 v) (K v) (hK v hv)
  choose! m hm using hm
  refine ⟨∏ v ∈ T, p v ^ m v, Finset.prod_pos fun v _ => pow_pos (hp0 v) _, ?_⟩
  intro x hx hxK
  apply h4
  intro w
  push_cast
  rw [map_mul]
  by_cases hw : w ∈ T
  · rw [← Finset.mul_prod_erase T (fun v => (p v : F) ^ m v) hw, map_mul, map_prod]
    have hrest : ∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v) ≤ 1 :=
      Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    have hmain : w.valuation F ((p w : F) ^ m w) * w.valuation F x ≤ 1 := by
      have h := hm w hw _ (hxK w hw)
      rw [← map_pow, ← map_mul, h3, map_mul] at h
      exact h
    calc w.valuation F ((p w : F) ^ m w) * (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
          w.valuation F x
        = (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
            (w.valuation F ((p w : F) ^ m w) * w.valuation F x) := by ac_rfl
      _ ≤ 1 * 1 := mul_le_mul' hrest hmain
      _ = 1 := one_mul 1
  · have hxw : w.valuation F x ≤ 1 := by
      have h : Valued.v (algebraMap F (Fv F w) x) ≤ 1 := hx w hw
      rwa [h3] at h
    have hN : w.valuation F (∏ v ∈ T, (p v : F) ^ m v) ≤ 1 := by
      rw [map_prod]
      exact Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    calc w.valuation F (∏ v ∈ T, (p v : F) ^ m v) * w.valuation F x ≤ 1 * 1 := mul_le_mul' hN hxw
      _ = 1 := one_mul 1
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.card_hermitian_matrices_mod_pow : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermMod | exact GlobalTheory.CompanionTheory.UnrDens.card_hermMod | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermMod <;> assumption)
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FinOpenGram

theorem finOpen : PositivityTheory.PfSWUS.SchInf.FinOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ n μ ν m hμ hν hm f hf hfin U hU hne
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  by_contra hcon
  push Not at hcon
  have hpos : ν U ≠ 0 := (hU.measure_pos ν hne).ne'
  have h2 := hm
  unfold GlobalTheory.CompanionTheory.SW.IsGramFib Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily at h2
  have hfib := h2.2.1 f hf
  have hle : (⊤ : ℝ≥0∞) * ν U ≤ ∫⁻ S, ∫⁻ X, f X ∂(m S) ∂ν := by
    rw [← lintegral_indicator_const hU.measurableSet]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ U
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← hfib] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

end GlobalTheory.CompanionTheory.SW.FinOpenGram
end
end

section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.newton_approximation_local_to_global : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | exact GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal <;> assumption)
end
