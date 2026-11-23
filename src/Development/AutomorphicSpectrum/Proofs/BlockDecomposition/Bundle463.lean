module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.FieldGenPf

open GlobalTheory.CompanionTheory.BruhatCell (cT_mul cT_one cT_zero cT_neg cT_cT isUnit_det_cT cT_inv cT_blk4 cT_eId cT_extB
  eId_mul_eId exists_blockMatrixTwoByTwoFin_eq is_siegel_parabolic_block_iff unitary_mul blockMatrixTwoByTwoFin_injective)

variable {K : Type} [Field K]

theorem exists_rows {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ (c : Matrix (Fin (Module.finrank K U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
      (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ IsCompl c a :=
  _root_.UpperTheory.Reformulated.B.ComplementSubspace.main U

theorem siegel_factor (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    {p : Matrix (Fin (n + n)) (Fin (n + n)) K} (hp : IsUnitary σ (Jm K n) p) (hs : IsSiegelP p) :
    ∃ X A : Matrix (Fin n) (Fin n) K, cT σ X = X ∧ IsUnit A.det ∧ p = nB X * mA σ A := by
  obtain ⟨A, B, C, E, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq p
  obtain rfl := (is_siegel_parabolic_block_iff A B C E).1 hs
  unfold IsUnitary EC.Jm at hp
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at hp
  obtain ⟨-, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective hp
  simp only [cT_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add,
    Matrix.neg_mul, neg_inj, neg_zero] at h2 h3 h4
  have hEA : cT σ E * A = 1 := h3
  have hAE : cT σ A * E = 1 := h2
  have hA : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hEA
  have hinv : (cT σ A)⁻¹ = E := Matrix.inv_eq_right_inv hAE
  have hAE' : A * cT σ E = 1 := mul_eq_one_comm.1 hEA
  have hEA' : E * cT σ A = 1 := mul_eq_one_comm.1 hAE
  have hBE : cT σ B * E = cT σ E * B := by
    have := h4
    rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at this
    exact this
  refine ⟨B * cT σ A, A, ?_, hA, ?_⟩
  · rw [cT_mul, cT_cT σ hσ]
    calc A * cT σ B = A * cT σ B * (E * cT σ A) := by rw [hEA', Matrix.mul_one]
      _ = A * (cT σ B * E) * cT σ A := by simp only [Matrix.mul_assoc]
      _ = (A * cT σ E) * B * cT σ A := by rw [hBE]; simp only [Matrix.mul_assoc]
      _ = B * cT σ A := by rw [hAE', Matrix.one_mul]
  · unfold nB mA
    rw [submatrix_fromBlocks_mul, hinv]
    simp [Matrix.mul_assoc, hAE]

theorem wr_word {n : ℕ} (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) :
    blk4 (1 - e) e (-e) (1 - e) =
      blk4 1 e 0 1 * blk4 0 1 (-1) 0 * blk4 1 e 0 1 * blk4 0 (-1) 1 0 * blk4 1 e 0 1 := by
  have s1 : blk4 1 e 0 1 * blk4 0 1 (-1) 0 = blk4 (-e) 1 (-1) 0 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s2 : blk4 (-e) 1 (-1) 0 * blk4 1 e 0 1 = blk4 (-e) (1 - e) (-1) (-e) := by
    rw [submatrix_fromBlocks_mul]; simp [he, sub_eq_add_neg, add_comm]
  have s3 : blk4 (-e) (1 - e) (-1) (-e) * blk4 0 (-1) 1 0 = blk4 (1 - e) e (-e) 1 := by
    rw [submatrix_fromBlocks_mul]; simp
  have s4 : blk4 (1 - e) e (-e) 1 * blk4 1 e 0 1 = blk4 (1 - e) e (-e) (1 - e) := by
    have h0 : (-e + 1) * e = 0 := by simp [Matrix.add_mul, he]
    rw [submatrix_fromBlocks_mul]; simp [Matrix.sub_mul, he, h0, sub_eq_add_neg, add_comm]
  rw [s1, s2, s3, s4]

theorem Jm_mul_mA_neg (σ : K →+* K) (n : ℕ) :
    Jm K n * mA σ (-1 : Matrix (Fin n) (Fin n) K) = blk4 0 (-1) 1 0 := by
  have h : (cT σ (-1 : Matrix (Fin n) (Fin n) K))⁻¹ = -1 := by
    rw [cT_neg, cT_one]; exact Matrix.inv_eq_right_inv (by simp)
  unfold EC.Jm mA
  rw [h, submatrix_fromBlocks_mul]; simp

theorem unitary_inv (σ : K →+* K) {N : ℕ} {J r : Matrix (Fin N) (Fin N) K} (hd : IsUnit r.det)
    (hr : IsUnitary σ J r) : IsUnitary σ J r⁻¹ := by
  unfold IsUnitary at *
  have h1 : cT σ r⁻¹ * cT σ r = 1 := by
    rw [cT_inv σ hd]; exact Matrix.nonsing_inv_mul _ (isUnit_det_cT σ hd)
  have h2 : r * r⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc cT σ r⁻¹ * J * r⁻¹ = cT σ r⁻¹ * (cT σ r * J * r) * r⁻¹ := by rw [hr]
    _ = (cT σ r⁻¹ * cT σ r) * J * (r * r⁻¹) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem fieldGen_of_bruhat : Bruhat → ∀ (K : Type) [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → (2 : K) ≠ 0 →
    ∀ n : ℕ, FieldGen K σ n := by
  intro hB K _ σ hσ h2 n T hmul hm hn hJ g hg hu
  choose c a hc ha using exists_rows (K := K) (n := n)
  obtain ⟨hrep, hex⟩ := hB K σ hσ h2 n c hc a ha
  obtain ⟨⟨U, b, hb⟩, hq, -⟩ := hex g hg hu
  obtain ⟨hrd, hru⟩ := hrep U b hb
  have hq' : IsSiegelP (g * (repMat σ b (a U))⁻¹) := hq
  have hTw : ∀ r, T (wr K n r) := by
    intro r
    have hne : ∀ r, T (nB (eId K n r)) := fun r => hn _ (cT_eId σ n r)
    have hJi : T (blk4 0 (-1) 1 0) := by
      rw [← Jm_mul_mA_neg σ n]
      refine hmul _ _ hJ (hm _ ?_)
      rw [Matrix.det_neg, Matrix.det_one]
      simp
    unfold wr
    rw [wr_word _ (eId_mul_eId n r)]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hne r) hJ) (hne r)) hJi) (hne r)
  have hTrep : T (repMat σ b (a U)) :=
    hmul _ _ (hmul _ _ (hTw _) (hn _ (by rw [cT_extB, hb]))) (hm _ (ha U).1)
  obtain ⟨X, A, hX, hA, hp⟩ := siegel_factor σ hσ (unitary_mul σ hu (unitary_inv σ hrd hru)) hq'
  have hTp : T (g * (repMat σ b (a U))⁻¹) := by
    rw [hp]; exact hmul _ _ (hn X hX) (hm A hA)
  have e : g = g * (repMat σ b (a U))⁻¹ * repMat σ b (a U) := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hrd, Matrix.mul_one]
  rw [e]
  exact hmul _ _ hTp hTrep

end GlobalTheory.CompanionTheory.EisCovar.FieldGenPf
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

theorem exists_radical_basis {K : Type*} [Field K] {r : ℕ} (B : Matrix (Fin r) (Fin r) K)
    (hd : B.det = 0) :
    ∃ (t k : ℕ) (e : Module.Basis (Fin t ⊕ Fin k) K (Fin r → K)), 0 < k ∧
      (∀ j, B *ᵥ e (Sum.inr j) = 0) ∧
      (∀ w : Fin t → K, B *ᵥ (∑ j, w j • e (Sum.inl j)) = 0 → w = 0) := by
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin r → K), N = LinearMap.ker B.mulVecLin := ⟨_, rfl⟩
  have hmemN : ∀ v, v ∈ N ↔ B *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl N
  obtain ⟨bN⟩ : Nonempty (Module.Basis (Fin (Module.finrank K N)) K N) := ⟨Module.finBasis K N⟩
  obtain ⟨bC⟩ : Nonempty (Module.Basis (Fin (Module.finrank K C)) K C) := ⟨Module.finBasis K C⟩
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (Fin (Module.finrank K C) ⊕ Fin (Module.finrank K N)) K (Fin r → K),
      e = (bC.prod bN).map (Submodule.prodEquivOfIsCompl C N hC.symm) := ⟨_, rfl⟩
  have he_inl : ∀ j, e (Sum.inl j) = (bC j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  have he_inr : ∀ j, e (Sum.inr j) = (bN j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  refine ⟨Module.finrank K C, Module.finrank K N, e, ?_, ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v, (hmemN v).mpr hv⟩, fun h => hv0 ?_⟩
    simpa using congrArg Subtype.val h
  · intro j
    rw [he_inr]
    exact (hmemN _).mp (bN j).2
  · intro w hw
    simp only [he_inl] at hw
    have hc : ((∑ j, w j • bC j : C) : Fin r → K) = ∑ j, w j • (bC j : Fin r → K) := by
      simp
    have hNmem : ((∑ j, w j • bC j : C) : Fin r → K) ∈ N := by
      rw [hmemN, hc]
      exact hw
    have h0 : ((∑ j, w j • bC j : C) : Fin r → K) = 0 :=
      Submodule.disjoint_def.mp hC.disjoint _ hNmem (Submodule.coe_mem _)
    funext j
    exact Fintype.linearIndependent_iff.mp bC.linearIndependent w (Submodule.coe_eq_zero.mp h0) j

theorem exists_blockNF {K : Type*} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {r : ℕ}
    (B : Matrix (Fin r) (Fin r) K) (hB : (B.map s)ᵀ = B) (hd : B.det = 0) :
    ∃ (P : Matrix (Fin r) (Fin r) K) (t : ℕ) (h : t < r), P.det ≠ 0 ∧
      (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0) ∧
      (((P.map s)ᵀ * B * P).submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0 := by
  obtain ⟨t, k, e, hk, hker, hinj⟩ := exists_radical_basis B hd
  have hcard : t + k = r := by
    have h1 := Module.finrank_eq_card_basis e
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm
  subst hcard
  have ht : t < t + k := Nat.lt_add_of_pos_right hk
  have hsplit : ∀ c : Fin t ⊕ Fin k, (∃ i', c = Sum.inl i') ∨ ∃ i', c = Sum.inr i' := by
    rintro (i' | i')
    · exact Or.inl ⟨i', rfl⟩
    · exact Or.inr ⟨i', rfl⟩
  have hinr : ∀ i : Fin (t + k), t ≤ i.1 → ∃ i', finSumFinEquiv.symm i = Sum.inr i' := by
    intro i hi
    rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
    · exfalso
      have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
      rw [hc, finSumFinEquiv_apply_left] at h1
      have h2 : i.1 = i'.1 := (congrArg Fin.val h1).symm
      have h3 := i'.isLt
      omega
    · exact ⟨i', hc⟩
  have hcast : ∀ j : Fin t, finSumFinEquiv.symm (Fin.castLE ht.le j) = Sum.inl j := by
    intro j
    have h1 : Fin.castLE ht.le j = Fin.castAdd k j := Fin.ext rfl
    rw [h1, finSumFinEquiv_symm_apply_castAdd]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (t + k)) (Fin (t + k)) K,
      ∀ a b, P a b = e (finSumFinEquiv.symm b) a :=
    ⟨Matrix.of fun a b => e (finSumFinEquiv.symm b) a, fun _ _ => rfl⟩
  have hBab : ∀ a b, s (B b a) = B a b := fun a b => by
    simpa using congrFun (congrFun hB a) b
  have hentry : ∀ i j, ((P.map s)ᵀ * B * P) i j =
      (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ e (finSumFinEquiv.symm j)) := by
    intro i j
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Matrix.map_apply, hP]
  have hrow : ∀ i' : Fin k, Matrix.vecMul (fun a => s (e (Sum.inr i') a)) B = 0 := by
    intro i'
    ext b
    have h0 : (B *ᵥ e (Sum.inr i')) b = 0 := by rw [hker i', Pi.zero_apply]
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    calc ∑ a, s (e (Sum.inr i') a) * B a b = ∑ a, s (B b a * e (Sum.inr i') a) :=
          Finset.sum_congr rfl fun a _ => by rw [map_mul, hBab, mul_comm]
      _ = s (∑ a, B b a * e (Sum.inr i') a) := (map_sum s _ _).symm
      _ = s ((B *ᵥ e (Sum.inr i')) b) := rfl
      _ = 0 := by rw [h0, map_zero]
  have hzero : ∀ i j : Fin (t + k), (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0 := by
    intro i j hij
    rw [hentry]
    rcases hij with hi | hj
    · obtain ⟨i', hi'⟩ := hinr i hi
      rw [hi', Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]
    · obtain ⟨j', hj'⟩ := hinr j hj
      rw [hj', hker j', dotProduct_zero]
  have hli : LinearIndependent K (fun b => e (finSumFinEquiv.symm b)) :=
    e.linearIndependent.comp _ finSumFinEquiv.symm.injective
  have hmv : ∀ v : Fin (t + k) → K, P *ᵥ v = ∑ b, v b • e (finSumFinEquiv.symm b) := by
    intro v
    ext a
    simp [Matrix.mulVec, dotProduct, hP, Finset.sum_apply, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    funext b
    exact Fintype.linearIndependent_iff.mp hli v (by rw [← hmv v]; exact hv) b
  have hPs : ((P.map s)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero s).mpr hPdet
  have hTy : ∀ i (y : Fin (t + k) → K),
      ((P.map s)ᵀ *ᵥ y) i = (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ y := by
    intro i y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hP]
  refine ⟨P, t, ht, hPdet, hzero, ?_⟩
  intro hB0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB0
  apply hw0
  apply hinj w
  obtain ⟨u, hu⟩ : ∃ u : Fin (t + k) → K, u = ∑ j, w j • e (Sum.inl j) := ⟨_, rfl⟩
  rw [← hu]
  have hexp : ∀ i, (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ u) =
      ∑ j, ((P.map s)ᵀ * B * P) i (Fin.castLE ht.le j) * w j := by
    intro i
    rw [hu, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hentry, hcast, mul_comm]
  by_contra hBu
  apply hPs
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨B *ᵥ u, hBu, ?_⟩
  funext i
  rw [hTy, Pi.zero_apply]
  rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
  · have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
    rw [hc, finSumFinEquiv_apply_left] at h1
    have hi : i = Fin.castLE ht.le i' := h1.symm.trans (Fin.ext rfl)
    rw [hexp, hi]
    have h2 := congrFun hw i'
    first
    | exact h2
    | (simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h2; exact h2)
  · rw [hc, Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem exists_congrH_isBlockNF (D : D7) (r : ℕ) (β : HermE D r) (hd : β.1.det = 0) :
    ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r),
      a.det ≠ 0 ∧ IsBlockNF t γ ∧ β = congrH a γ := by
  obtain ⟨P, t, ht, hP, hzero, hblock⟩ := NF.exists_blockNF (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun x => star_star x) β.1 β.2 hd
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, t, congrH P β, ?_, ⟨ht, hzero, hblock⟩, ?_⟩
  · intro h0
    have h1 := congrArg Matrix.det (Matrix.nonsing_inv_mul P hu)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  · apply Subtype.ext
    change β.1 = ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
      ((P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ * β.1 * P) * P⁻¹
    have h1 : ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
        (P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv P hu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem ev_dehomog_of_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  intro m n c f a hf w z H hw
  have hmem : ∀ k, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := fun k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) hw
  have hX : ∀ q, GlobalTheory.CxPts.evHom hw (dehomog c (X q)) = z q / z ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    rw [← GlobalTheory.CxPts.ev_eq hw]
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [GlobalTheory.CxPts.ev_res _ hw]
    exact (H k (c k)).2 i (hmem k)
  have hφ : (GlobalTheory.CxPts.evHom hw).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp
    · simpa using hX q
  have hv : GlobalTheory.CxPts.evHom hw (dehomog c f) =
      eval₂ (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) f := by
    simpa using congrArg (fun φ => φ f) hφ
  rw [GlobalTheory.CxPts.ev_eq hw, hv, MvPolynomial.eval_map, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hden : ∏ q : Σ k, Bk n k, z ⟨q.1, c q.1⟩ ^ e q = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Bk n k => e ⟨k, i⟩) (z ⟨k, c k⟩)).trans (by rw [hf e he k])
  simp only [div_pow, Finset.prod_div_distrib, hden]
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.MixZ
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

theorem latS_isOpen_isCompact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  intro E _ _ _ S B hO hI
  have hc : ∀ w : Pl E, Continuous (pLoc E w) := fun w => RestrictedProduct.continuous_eval w
  have heq : (latS S B : Set (Af E)) =
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∩
        ⋂ w ∈ S, (pLoc E w) ⁻¹' (B w : Set (w.adicCompletion E)) := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_, ?_⟩
      · by_cases hw : w ∈ S
        · exact hI w hw (h2 w hw)
        · exact h1 w hw
      · exact Set.mem_iInter₂.2 fun w hw => h2 w hw
    · rintro ⟨h1, h2⟩
      exact ⟨fun w _ => GroundTheory.Global.mem_integralFiniteAdeles.1 h1 w,
        fun w hw => Set.mem_iInter₂.1 h2 w hw⟩
  rw [heq]
  constructor
  · exact GroundTheory.Global.isOpen_integralFiniteAdeles.inter
      (isOpen_biInter_finset fun w hw => (hO w hw).preimage (hc w))
  · refine (GroundTheory.Global.isCompact_integralFiniteAdeles E).inter_right ?_
    refine isClosed_biInter fun w hw => IsClosed.preimage (hc w) ?_
    exact AddSubgroup.isClosed_of_isOpen (B w) (hO w hw)

end GlobalTheory.CompanionTheory.CutOff
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff.Split

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def rowEquiv (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) :
    (Fin k → InfiniteAdeleRing E) ≃ᵐ (Fin k → Cinf E) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := (infEq E).symm.toEquiv
      measurable_toFun := (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E).measurable
      measurable_invFun := (continuous_infEq E).measurable }

theorem nuInf_eq (k : ℕ) :
    nuInf E k = (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).map (rowEquiv E k) := rfl

theorem integral_split {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ) :
    ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  have hmp := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)
    (fun _ => GroundTheory.Global.infiniteAdeleMeasure E) (fun _ => GroundTheory.Global.finiteAdeleMeasure E)
  haveI : SFinite (nuFin E k) := by unfold nuFin; infer_instance
  have e : (fun y : Fin k → Ad E => A (fun i => pInf E (y i)) * B (fun i => pFin E (y i))) =
      fun x => (A ∘ rowEquiv E k) ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).1 *
        B ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).2 := by
    funext y
    rfl
  have h1 : ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      ∫ z, (A ∘ rowEquiv E k) z.1 * B z.2 ∂((Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).prod
        (nuFin E k)) := by
    rw [e]
    exact (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z => (A ∘ rowEquiv E k) z.1 * B z.2))
  rw [h1, integral_prod_mul, nuInf_eq, integral_map_equiv]
  rfl

end GlobalTheory.CompanionTheory.CutOff.Split
end
end
