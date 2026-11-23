module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumGramInr
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
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzPlus_firstProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph1 g (HermSp.ZZplusOf M Zh T T' a b) =
      (g.q : F)⁻¹ * ph1 g (Zh a b) + (if a = Fin.last r ∧ b = Fin.last r then T / (g.q : F) else 0) := by
  have h1 : ∀ x : E, ph1 g x = (g.e x).1 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h1, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.fst_zero, Prod.fst_sub,
    sub_zero, add_zero] <;> ring

theorem zzPlus_secondProj_corner (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (a b : Fin (r + 1)) :
    ph2 g (HermSp.ZZplusOf M Zh T T' a b) =
      -((g.q : F)⁻¹ * ph2 g (Zh b a)) + (if a = Fin.last r ∧ b = Fin.last r then -(T' / (g.q : F)) else 0) := by
  have h2 : ∀ x : E, ph2 g x = (g.e x).2 := fun x => rfl
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply]
  split_ifs with hab <;> simp only [h2, map_sub, AlgEquiv.apply_symm_apply, map_zero, Prod.snd_zero, Prod.snd_sub,
    sub_zero, add_zero] <;> ring

def lamV (g : SplitG M.L) (m : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => -(ph2 g (m a)) / (g.q : F)) (fun a => ph1 g (m a) / (g.q : F))

theorem firstProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph1 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph1 g (f j : E) := by

  rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem secondProj_ring_sum (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → M.R) :
    ph2 g ((∑ j ∈ s, f j : M.R) : E) = ∑ j ∈ s, ph2 g (f j : E) := by

  rw [AddSubmonoidClass.coe_finsetSum, map_sum]

theorem firstProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph1 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).1 = c
  rw [AlgEquiv.commutes]
  rfl

theorem secondProj_diagonalEmbed (hs : M.split = some g) (c : 𝒪[F]) : ph2 g ((dgR hs c : M.R) : E) = c := by
  show (g.e (algebraMap F E (c : F))).2 = c
  rw [AlgEquiv.commutes]
  rfl

theorem uV_llMap (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : M.Mat (r + 1)) (TT : M.R) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (hTT : g.e (TT : E) = (T, T')) (m : Fin (r + 1) → M.R) :
    uV g (llMap hs Z TT m) = Matrix.vecMul (lamV g m) (gHat g Zh T T') := by
  have hZe : ∀ i j, ((Z.Z i j : M.R) : E) = HermSp.ZZplusOf M Zh T T' i j := fun i j => by
    rw [← hZ]; rfl
  have hT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hTT]
  have hT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hTT]
  have hq := q_ne g
  obtain ⟨Zf, rfl⟩ : ∃ Zf : Fin (r + 1) → Fin (r + 1) → E, Matrix.of Zf = Zh := ⟨Zh, rfl⟩
  have hsum1 : ∀ i, ∑ x, (g.e (Zf i x)).1 * (g.e (m x : E)).1 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).1 * (g.e (Zf i x)).1 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum2 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 * (g.q : F)⁻¹ =
      ∑ x, (g.q : F)⁻¹ * (g.e (m x : E)).2 * (g.e (Zf x i)).2 := fun i => Finset.sum_congr rfl fun x _ => by ring
  have hsum3 : ∀ i, ∑ x, (g.e (Zf x i)).2 * (g.e (m x : E)).2 / (g.q : F) =
      ∑ x, (g.e (m x : E)).2 * (g.e (Zf x i)).2 / (g.q : F) := fun i => Finset.sum_congr rfl fun x _ => by ring
  funext k
  rcases k with i | i
  · simp only [uV, Sum.elim_inl, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, firstProj_ring_sum,
      hZe, zzPlus_firstProj_corner hs, hT1, firstProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inr,
      gHat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
  · simp only [uV, Sum.elim_inr, llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, map_sub, map_mul, secondProj_ring_sum,
      hZe, zzPlus_secondProj_corner hs, hT2, secondProj_diagonalEmbed, trO_coe, Matrix.vecMul, Fintype.sum_sum_type, lamV, Sum.elim_inl,
      gHat, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.map_apply, eV]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [Pi.single_apply, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)
    · simp [Pi.single_apply, hi, firstProj_apply, secondProj_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum, ite_and]
      field_simp
      first
        | done
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; done)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring)
        | (simp only [div_eq_mul_inv, neg_mul, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]; ring_nf)

theorem lamV_dot_mem (hs : M.split = some g) (m w : Fin (r + 1) → M.R) :
    dotProduct (lamV g m) (uV g w) ∈ 𝒪[F] := by
  classical
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  unfold dotProduct lamV uV
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply sum_mem
  intro a _
  obtain ⟨hm1, hm2, cm, hcm⟩ := comp_of_mem_R hs (m a).2
  obtain ⟨hw1, hw2, cw, hcw⟩ := comp_of_mem_R hs (w a).2
  have key : -(ph2 g (m a : E)) / (g.q : F) * ph1 g (w a : E) + ph1 g (m a : E) / (g.q : F) * ph2 g (w a : E) =
      (cm : F) * (g.e (w a : E)).2 - (g.e (m a : E)).2 * (cw : F) := by
    show -((g.e (m a : E)).2) / (g.q : F) * (g.e (w a : E)).1 +
      (g.e (m a : E)).1 / (g.q : F) * (g.e (w a : E)).2 = _
    have e1 : (g.e (m a : E)).1 = (g.e (m a : E)).2 + (g.q : F) * cm := by linear_combination hcm
    have e2 : (g.e (w a : E)).1 = (g.e (w a : E)).2 + (g.q : F) * cw := by linear_combination hcw
    rw [e1, e2]
    field_simp
    ring
  rw [key]
  exact sub_mem (mul_mem cm.2 hw2) (mul_mem hm2 cw.2)

theorem dot_inv_vecMul {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (lam x : n → F) : dotProduct (Matrix.vecMul lam G) (Matrix.mulVec G⁻¹ x) = dotProduct lam x := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]

theorem dot_inv_mulVec {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n F) (hG : IsUnit G.det)
    (mu x : n → F) : dotProduct x (Matrix.mulVec G⁻¹ (Matrix.mulVec G mu)) = dotProduct x mu := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]

theorem gHat_cj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    gHat g (Zh.map M.L.cj) T T' = (gHat g Zh T T').transpose := by
  have hcj1 : ∀ x : E, ph1 g (M.L.cj x) = ph2 g x := fun x => by
    show (g.e (M.L.cj x)).1 = (g.e x).2
    rw [g.e_cj]
    rfl
  have hcj2 : ∀ x : E, ph2 g (M.L.cj x) = ph1 g x := fun x => by
    show (g.e (M.L.cj x)).2 = (g.e x).1
    rw [g.e_cj]
    rfl
  unfold gHat
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_transpose]
  congr 1
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl
  · ext a b
    simp only [Matrix.map_apply, hcj2]
  · ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, hcj1]
  · ext a b
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    exact if_congr and_comm rfl rfl

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem isoB_of (hs : M.split = some g) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)} {TT : M.R}
    (hG₁ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T)
      (algebraMap F E T')).det)
    (hG₂ : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T)
      (algebraMap F E T')).det)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (h : ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
      θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
      dotProduct (uV g l₂) (Matrix.mulVec (gHat g Zh₂ T T')⁻¹ (uV g w₂)) -
        dotProduct (uV g l) (Matrix.mulVec (gHat g Zh₁ T T')⁻¹ (uV g w)) ∈ 𝒪[F]) :
    IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ := by
  intro l l₂ w w₂ hl hw
  apply mem_O_of_comp g
  · rw [map_sub, Prod.fst_sub, ← firstProj_apply, ← firstProj_apply, splitForm_iota_firstProj hs Zh₂ T T' hG₂,
      splitForm_iota_firstProj hs Zh₁ T T' hG₁]
    exact h l l₂ w w₂ hl hw
  · rw [map_sub, Prod.snd_sub, ← secondProj_apply, ← secondProj_apply, splitForm_iota_secondProj, splitForm_iota_secondProj, sub_zero]
    exact zero_mem _

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_of_rel (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (Y W : Ix r → O) (c : Ix r → E)
    (hY : ∀ j, (Y j : E) = ∑ i, c i * gramC cj Z T T' i j) :
    formC O cj Z T T' Y W = ∑ j, c j * cj (W j) := by
  have hc : Matrix.vecMul (fun j => (Y j : E)) (gramC cj Z T T')⁻¹ = c := by
    have hYv : (fun j => (Y j : E)) = Matrix.vecMul c (gramC cj Z T T') := by
      funext j
      rw [hY j]
      rfl
    rw [hYv, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]
  unfold formC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, ← congrFun hc j]
  rfl

def cvec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y : Ix r → O) : Ix r → E :=
  Sum.elim
    (fun a => (∑ j, cj (Z⁻¹ j a) * (Y (Sum.inr j) : E)) +
      T' * lamC Z (fun j => (Y (Sum.inl j) : E)) * cj (Z⁻¹ (Fin.last r) a))
    (fun b => (Z⁻¹.mulVec (fun j => (Y (Sum.inl j) : E))) b +
      T * lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) * Z⁻¹ b (Fin.last r))

theorem cvec_gram (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hu : IsUnit Z.det) (hκ : Z⁻¹ (Fin.last r) (Fin.last r) = 0) (T T' : E) (Y : Ix r → O) :
    ∀ j, (Y j : E) = ∑ i, cvec O cj Z T T' Y i * gramC cj Z T T' i j := by
  have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hu
  have hZ' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hu
  have cl : cvec O cj Z T T' Y (Sum.inl (Fin.last r)) =
      lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) := by
    simp only [cvec, Sum.elim_inl, hκ, map_zero, mul_zero, add_zero, lamStarC]
  have cr : cvec O cj Z T T' Y (Sum.inr (Fin.last r)) = lamC Z (fun j => (Y (Sum.inl j) : E)) := by
    simp only [cvec, Sum.elim_inr, hκ, mul_zero, add_zero, lamC]
  intro j
  rcases j with j | j
  · rw [sum_gram_inl, cl]
    have a1 : ∑ b, Z j b * Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E)) b = (Y (Sum.inl j) : E) := by
      have := congrFun (show Z.mulVec (Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E))) =
        (fun k => (Y (Sum.inl k) : E)) by rw [Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]) j
      simpa only [Matrix.mulVec, dotProduct] using this
    have a2 : ∑ b, Z j b * Z⁻¹ b (Fin.last r) = if j = Fin.last r then 1 else 0 := by
      have := congrFun (congrFun hZ j) (Fin.last r)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have e1 : ∑ b, Z j b * cvec O cj Z T T' Y (Sum.inr b) =
        (Y (Sum.inl j) : E) + T * lamStarC cj Z (fun k => (Y (Sum.inr k) : E)) *
          (if j = Fin.last r then 1 else 0) := by
      simp only [cvec, Sum.elim_inr]
      rw [← a1, ← a2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1]
    split_ifs <;> ring
  · rw [sum_gram_inr, cr]
    have a1 : ∀ k, ∑ a, cj (Z a j) * cj (Z⁻¹ k a) = if k = j then 1 else 0 := by
      intro k
      have := congrFun (congrFun hZ' k) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this

      rw [← map_one cj, ← map_zero cj, ← apply_ite cj, ← this, map_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [map_mul, mul_comm])
    have e1 : ∑ a, cj (Z a j) * cvec O cj Z T T' Y (Sum.inl a) =
        (Y (Sum.inr j) : E) + T' * lamC Z (fun k => (Y (Sum.inl k) : E)) *
          (if Fin.last r = j then 1 else 0) := by
      simp only [cvec, Sum.elim_inl]
      rw [← a1 (Fin.last r)]
      have a3 : ∑ a, cj (Z a j) * ∑ k, cj (Z⁻¹ k a) * (Y (Sum.inr k) : E) = (Y (Sum.inr j) : E) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ k, ∑ a, cj (Z a j) * (cj (Z⁻¹ k a) * (Y (Sum.inr k) : E)) =
            (if k = j then 1 else 0) * (Y (Sum.inr k) : E) := by
          intro k
          rw [← a1 k, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        simp_rw [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← a3, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e1]
    by_cases hj : j = Fin.last r
    · subst hj; simp only [if_true]; ring
    · rw [if_neg hj, if_neg (Ne.symm hj)]; ring

theorem formC_eq (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (hκ : (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det) (Y W : Ix r → O) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) +
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) +
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  rw [formC_of_rel O cj _ T T' hG Y W _ (cvec_gram O cj hcj _ hu hκ T T' Y), Fintype.sum_sum_type]
  simp only [cvec, Sum.elim_inl, Sum.elim_inr, add_mul, Finset.sum_add_distrib]
  have s1 : ∑ a, (∑ k, cj ((Z.map O.subtype)⁻¹ k a) * (Y (Sum.inr k) : E)) * cj (W (Sum.inl a) : E) =
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) := by

    simp only [bRaw, map_sum, map_mul, hcj, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => by ring))
  have s3 : ∑ b, (Z.map O.subtype)⁻¹.mulVec (fun j => (Y (Sum.inl j) : E)) b * cj (W (Sum.inr b) : E) =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) := by
    simp only [bRaw]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  have s2 : ∑ a, T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) =
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) := by
    have e : cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) =
        ∑ a, cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) := by

      simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have s4 : ∑ b, T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) =
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
    have e : cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) =
        ∑ b, (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) := by

      simp only [lamStarC, map_sum, map_mul, hcj]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  linear_combination s1 + s2 + s3 + s4

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end
