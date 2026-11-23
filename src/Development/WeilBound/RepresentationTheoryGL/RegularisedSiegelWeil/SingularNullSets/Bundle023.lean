module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle095
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CutSupp
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle352
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle010

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIkSch

theorem isCompact_K {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    IsCompact (l.K : Set (GA D T)) := by
  exact (GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c (fun v hv => GlobalTheory.Core.Rk.IP.Model.isSplit_two v hv) hl.2.2) l hl).2.1

end PositivityTheory.Rg.Rsw.L.LIkSch

namespace PositivityTheory.Rg.Rsw.L

theorem ikSch : IkSch := by
  intro D n t B W d I θ hθ Φ hΦ
  have hK : IsCompact (I.l.K : Set (GA D B)) := LIkSch.isCompact_K d I.good
  have h1 := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK Φ hΦ
  refine ⟨h1, ?_⟩
  obtain ⟨𝓕, h𝓕⟩ := I.cov₁
  exact GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz D θ hθ B W t n d I.μ₁ 𝓕 h𝓕 _ h1

end PositivityTheory.Rg.Rsw.L
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L


open UnitaryGroupMatrix in
theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LMajor in
theorem major : IdemEx → GoodEv → BumpEx → Major := by
  intro _ _ hB D θ hθ a b S e he Φ hΦ hG
  obtain ⟨k, f, M, hM, hdom⟩ := domBound θ hθ Φ hΦ
  obtain ⟨-, K, hK, hmaj⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ a b Φ (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ a b Φ hΦ)
  obtain ⟨C0, hC0⟩ := hmaj 0
  have hbox : ∀ x, Φ x ≠ 0 → GlobalTheory.Unf.InBox K x := by
    intro x hx
    by_contra hb
    have h := hC0 x
    rw [GlobalTheory.Unf.maj, if_neg hb, mul_zero] at h
    exact hx (norm_le_zero_iff.mp h)
  obtain ⟨F₀, hF₀, hcut⟩ := schMajor f
  obtain ⟨Φ₀, hΦ₀, hG₀, hpos, heq⟩ := bumpMaj hB θ hθ he K hK F₀ hF₀
  refine ⟨Φ₀, hΦ₀, hG₀, hpos, fun ε hε => ?_⟩
  have hMk : 0 < M * k + 1 := by have := mul_nonneg hM (Nat.cast_nonneg (α := ℝ) k); linarith
  obtain ⟨c, hct, hcc, hcb⟩ := hcut (ε / (M * k + 1)) (div_pos hε hMk)
  refine ⟨fun x => c (cA θ x) * Φ x, GlobalTheory.T.temperate_multiplier_preserves_schwartz D θ a b c hct Φ hΦ, good_mul θ he hG c,
    cutSupp θ hθ K hK Φ hbox c hcc, fun x => ?_⟩
  show ‖Φ x - c (cA θ x) * Φ x‖ ≤ ε * (Φ₀ x).re
  rw [show Φ x - c (cA θ x) * Φ x = (1 - c (cA θ x)) * Φ x by ring, norm_mul]
  by_cases h0 : Φ x = 0
  · rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hε.le (hpos x).1
  have hx : IntOff S x := by
    by_contra hx
    have h := hG x
    rw [if_neg hx] at h
    exact h0 h
  rw [heq x hx (hbox x h0)]
  have hF : 0 ≤ (F₀ (cA θ x)).re := (hF₀ _).1
  calc ‖1 - c (cA θ x)‖ * ‖Φ x‖ ≤ ‖1 - c (cA θ x)‖ * (M * ∑ i, ‖f i (cA θ x)‖) :=
        mul_le_mul_of_nonneg_left (hdom x) (norm_nonneg _)
    _ = M * ∑ i, ‖f i (cA θ x)‖ * ‖1 - c (cA θ x)‖ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ M * ∑ _i : Fin k, ε / (M * k + 1) * (F₀ (cA θ x)).re := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcb i _) hM
    _ = (M * k) / (M * k + 1) * (ε * (F₀ (cA θ x)).re) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 1 * (ε * (F₀ (cA θ x)).re) := by
        gcongr
        rw [div_le_one hMk]
        linarith
    _ = ε * (F₀ (cA θ x)).re := one_mul _

end PositivityTheory.Rg.Rsw.L

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

variable {D : D7} {n : ℕ}

theorem matHom_proj_val (v : Pl D) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 = (mat g).map (cv D v) := by
  rw [GlobalTheory.AdelicU.matHom_proj]; rfl

theorem matHom_projArch_val (w : InfinitePlace D.host.F) (g : G D n) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (projArch D.sp.cm.sig (Jst D n) w g)).1 =
      (mat g).map (compInf D.host.F D.host.E w) := by
  rw [GlobalTheory.AdelicU.matHom_projArch]; rfl

theorem block_matrix_diagonal_one_eq_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem block_matrix_entry_property {R : Type} [CommRing R] (S : Subring R) {a b c d : Matrix (Fin n) (Fin n) R}
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S) (hc : ∀ i j, c i j ∈ S) (hd : ∀ i j, d i j ∈ S) (i j : Fin (n + n)) :
    blk4 a b c d i j ∈ S := by
  unfold blk4
  simp only [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i' | i' <;> rcases finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  exacts [ha _ _, hb _ _, hc _ _, hd _ _]

theorem map_mat_nb {nb : hermA D n → G D n} (hnb : IsNMap nb) {S : Type} [CommRing S] (f : AE D →+* S) (x : hermA D n) :
    (mat (nb x)).map f = blk4 1 (x.1.map f) 0 1 := by
  rw [hnb x, GlobalTheory.CompanionTheory.FourierN.blk4_map_alt, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]

theorem proj_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) = 0) : proj D.sp.cm.sig (Jst D n) v (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_proj_val, map_mat_nb hnb]
  have : x.1.map (cv D v) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem projArch_nb_eq_one {nb : hermA D n → G D n} (hnb : IsNMap nb) (w : InfinitePlace D.host.F) {x : hermA D n}
    (hx : ∀ i j, compInf D.host.F D.host.E w (x.1 i j) = 0) : projArch D.sp.cm.sig (Jst D n) w (nb x) = 1 := by
  refine GlobalTheory.AdelicU.matHom_injective _ _ _ (Units.ext ?_)
  rw [map_one, Units.val_one, matHom_projArch_val, map_mat_nb hnb]
  have : x.1.map (compInf D.host.F D.host.E w) = 0 := Matrix.ext fun i j => hx i j
  rw [this, block_matrix_diagonal_one_eq_one]

theorem nb_mem_atPts {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hinf : ∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) (hoff : ∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) :
    nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} :=
  GlobalTheory.AdelicU.mem_atPts.2 ⟨GlobalTheory.AdelicU.mem_finPts_iff_forall.2 fun w => projArch_nb_eq_one hnb w (hinf w),
    fun v' hv' => proj_nb_eq_one hnb v' (hoff v' (by simpa using hv'))⟩

theorem nb_neg {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n) : nb (-x) = (nb x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← GlobalTheory.CompanionTheory.FourierN.nb_add hnb, neg_add_cancel, GlobalTheory.CompanionTheory.FourierN.nb_zero hnb])

theorem proj_nb_entry {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {y : hermA D n}
    (hy : ∀ i j, cv D v (y.1 i j) ∈ intLoc D.host.F D.host.E v) (i j : Fin (n + n)) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (nb y))).1 i j ∈ intLoc D.host.F D.host.E v := by
  rw [matHom_proj_val, map_mat_nb hnb]
  refine block_matrix_entry_property _ (fun a b => ?_) (fun a b => hy a b) (fun a b => ?_) (fun a b => ?_) i j
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact zero_mem _
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem proj_nb_mem_stabLoc {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n}
    (hx : ∀ i j, cv D v (x.1 i j) ∈ intLoc D.host.F D.host.E v) :
    proj D.sp.cm.sig (Jst D n) v (nb x) ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  refine GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.2 ⟨proj_nb_entry hnb v hx, ?_⟩
  have e : (proj D.sp.cm.sig (Jst D n) v (nb x))⁻¹ = proj D.sp.cm.sig (Jst D n) v (nb (-x)) := by
    rw [nb_neg hnb, map_inv]
  rw [e]
  refine proj_nb_entry hnb v fun i j => ?_
  have h1 : cv D v ((-x).1 i j) = -cv D v (x.1 i j) := RingHom.map_neg (cv D v) (x.1 i j)
  rw [h1]
  exact neg_mem (hx i j)

theorem mem_KAt_of {v : Pl D} {y : G D n}
    (h1 : y ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))) (h2 : y ∈ atPts D.sp.cm.sig (Jst D n) {v}) :
    y ∈ KAt D n v := by
  refine Subgroup.mem_inf.2 ⟨?_, h2⟩
  show y ∈ levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
  refine GlobalTheory.AdelicU.mem_levelAll.2 ⟨GlobalTheory.AdelicU.mem_levelOpen.1 h1, fun w => ?_⟩
  rw [GlobalTheory.AdelicU.mem_finPts_iff_forall.1 (GlobalTheory.AdelicU.mem_atPts.1 h2).1 w]
  exact one_mem _

theorem nb_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) (v : Pl D) {x : hermA D n} (hx : IntAt v x) :
    nb x ∈ KAt D n v := by
  refine mem_KAt_of (GlobalTheory.AdelicU.mem_levelOpen.2 fun v' => ?_) (nb_mem_atPts hnb v hx.1 hx.2.1)
  by_cases h : v' = v
  · subst h; exact proj_nb_mem_stabLoc hnb _ hx.2.2
  · rw [proj_nb_eq_one hnb v' (hx.2.1 v' h)]; exact one_mem _

theorem commute_of_atPts {v : Pl D} {x g : G D n} (hx : x ∈ atPts D.sp.cm.sig (Jst D n) {v})
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : x * g = g * x :=
  (GlobalTheory.AdelicU.commute_atPts_awayPts _ _ hx (GlobalTheory.AdelicU.mem_awayPts.2 fun u hu => by
    rw [Finset.mem_singleton.1 hu]; exact hg)).eq

def lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : Subgroup (G D n) :=
  ⨅ x : s, (levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))).comap (MulAut.conj (nb x.1)⁻¹).toMonoidHom

theorem isOpen_lev (nb : hermA D n → G D n) (s : Finset (hermA D n)) : IsOpen (lev nb s : Set (G D n)) := by
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := GlobalTheory.AdelicU.isLattice_stdLattice
  rw [lev, Subgroup.coe_iInf]
  refine isOpen_iInter_of_finite fun x => ?_
  rw [Subgroup.coe_comap]
  exact (GlobalTheory.AdelicU.isOpen_levelOpen _ _ _).preimage ((continuous_mul_const _).comp (continuous_const_mul _))

theorem conj_mem_KAt {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {k : G D n}
    (hk : k ∈ lev nb C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) {x : hermA D n} (hx : x ∈ C.s) :
    (nb x)⁻¹ * k * nb x ∈ KAt D n v := by
  have h1 := Subgroup.mem_iInf.1 hk ⟨x, hx⟩
  rw [Subgroup.mem_comap] at h1
  have hat := nb_mem_atPts hnb v (C.inf x hx) (C.off x hx)
  refine mem_KAt_of ?_ (mul_mem (mul_mem (inv_mem hat) hkv) hat)
  simpa [MulAut.conj_apply] using h1

end PositivityTheory.Rg.Rsw.L.LCutLow

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFourierPt

variable {D : D7} {n : ℕ}

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : Matrix (Fin n) (Fin n) D.host.E)
    (x : Mx D n n) : conj (pch ψ x (rat a)) = ψ (-GlobalTheory.CompanionTheory.FourierN.pr a x) := by
  have e : pch ψ x (rat a) = ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) := by
    rw [pch, GlobalTheory.CompanionTheory.FourierN.pr]
    congr 2
    exact Matrix.trace_mul_comm _ _
  rw [e, AddChar.map_neg_eq_inv]
  have hn : ‖ψ (GlobalTheory.CompanionTheory.FourierN.pr a x)‖ = 1 := hψ.2.1 _
  have hne : ψ (GlobalTheory.CompanionTheory.FourierN.pr a x) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

end PositivityTheory.Rg.Rsw.L.LFourierPt

namespace PositivityTheory.Rg.Rsw.L

open LFourierPt


theorem fourierPt : FourierPt := by
  intro D n ψ hψ lam 𝓖 hC f hf hper hco
  obtain ⟨hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) :=
    GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (hermA D n) (ratHerm D n) K hK hcov
    (GlobalTheory.CompanionTheory.FourierN.hermSub D n) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩),
      fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lam 𝓖 hlam hFD f hf hper
    (fun a => by
      have h := hco ⟨a.1, a.2⟩
      refine (integral_congr_ae (.of_forall fun x => ?_)).trans h
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1) * f x = f x * conj (pch ψ x.1 (rat a.1))
      rw [conj_pch hψ, mul_comm])

end PositivityTheory.Rg.Rsw.L

end
end
