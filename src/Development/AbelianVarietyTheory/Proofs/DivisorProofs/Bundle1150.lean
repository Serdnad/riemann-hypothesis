module

public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalToGlobal.GlobalTheory.PlacesP
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.LocalRingCardinality.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial
open scoped Pointwise

namespace GlobalTheory.PartsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Poly

variable {K L : Type} [Field K] [Field L]

theorem dualPoly_comp {a : K} (ha : a ≠ 0) (s : K) (p : K[X]) :
    dualPoly s (p.comp (C a⁻¹ * X)) = dualPoly (s * a) p := by
  have hd : (p.comp (C a⁻¹ * X)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha), mul_one]
  have hl : (p.comp (C a⁻¹ * X)).leadingCoeff = p.leadingCoeff * a⁻¹ ^ p.natDegree := by
    rw [leadingCoeff, hd, comp_C_mul_X_coeff, leadingCoeff]
  ext i
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_dualPoly_of_le _ _ (hd ▸ hi), coeff_dualPoly_of_le _ _ hi, hl, hd, comp_C_mul_X_coeff]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow]
    have h1 : a⁻¹ ^ i * a ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    have h2 : a⁻¹ ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
    have h3 : (a⁻¹ ^ i)⁻¹ = a ^ i := by rw [inv_pow, inv_inv]
    rw [mul_inv, mul_inv, h3]
    field_simp
  · have hi' := not_le.1 hi
    rw [coeff_dualPoly_of_lt _ _ (hd ▸ hi'), coeff_dualPoly_of_lt _ _ hi']

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → K) (i : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i =
      if i ≤ n then (-1) ^ i * (q : K) ^ (i * (i - 1) / 2) * a i else 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

theorem tri_add (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem heckePolyOf_dual {n q : ℕ} (hq : (q : K) ≠ 0) {a b : ℕ → K} (h0 : a 0 = 1)
    (h : ∀ k ≤ n, a n * b k = a (n - k)) :
    Formalism.L2.Col.heckePolyOf n q b = dualPoly ((q : K) ^ (n - 1)) (Formalism.L2.Col.heckePolyOf n q a) := by
  have hn : a n ≠ 0 := by
    have := h n le_rfl
    rw [Nat.sub_self, h0] at this
    exact left_ne_zero_of_mul_eq_one this
  have htop : (Formalism.L2.Col.heckePolyOf n q a).coeff n ≠ 0 := by
    rw [coeff_heckePolyOf, if_pos le_rfl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hq)) hn
  have hd : (Formalism.L2.Col.heckePolyOf n q a).natDegree = n :=
    le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun i hi => by rw [coeff_heckePolyOf, if_neg (not_le.2 hi)])
      (le_natDegree_of_ne_zero htop)
  ext i
  by_cases hi : i ≤ n
  · rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hi), leadingCoeff, hd, eq_inv_mul_iff_mul_eq₀ htop,
      coeff_heckePolyOf, coeff_heckePolyOf, coeff_heckePolyOf, if_pos le_rfl, if_pos hi, if_pos (Nat.sub_le _ _),
      ← h i hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    have e := congrArg (fun m => (q : K) ^ m) (tri_add i j)
    simp only [pow_add] at e
    have e2 : ((-1 : K) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    rw [pow_add]
    linear_combination ((-1 : K) ^ j * a (i + j) * b i * ((-1) ^ i * (-1) ^ i)) * e +
      ((-1 : K) ^ j * a (i + j) * b i * ((q : K) ^ (j * (j - 1) / 2) * (q : K) ^ ((i + j - 1) * i))) * e2
  · rw [coeff_dualPoly_of_lt _ _ (by rw [hd]; exact not_le.1 hi), coeff_heckePolyOf, if_neg hi]

end Poly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Label

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F)
include hs h

variable {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Label

section Ties

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D}
  {jE : D.what₂.EE →ₗ[ℂ] R.HE.H} {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Ties

section Main

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X}

end Main

end GlobalTheory.PartsCompare

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mulVec_mem (S : Subring R) (u : Matrix m m S) (x : m → R) (hx : ∀ i, x i ∈ S) (i : m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem frame_inv (S : Subring R) (β : GL n R) (β' : GL m R) (c : n ≃ m) (U : GL m R) (u u' : Matrix m m S)
    (hu : U.val = u.map S.subtype) (hu' : (U⁻¹).val = u'.map S.subtype) (j : Matrix m n R)
    (hj : j * β.val = (β' * U).val.submatrix id c) :
    (∃ j' : Matrix n m R, j * j' = 1 ∧ j' * j = 1) ∧
      ∀ x : n → R, (∀ i, (β⁻¹).val.mulVec x i ∈ S) ↔ ∀ i, (β'⁻¹).val.mulVec (j.mulVec x) i ∈ S := by
  have hj2 : j = (β' * U).val.submatrix id c * (β⁻¹).val := by
    rw [← hj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨⟨β.val * ((β' * U)⁻¹).val.submatrix c id, ?_, ?_⟩, fun x => ?_⟩
  · rw [← Matrix.mul_assoc, hj, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_id_id]
  · have h1 : ((β' * U)⁻¹).val.submatrix c id * (β' * U).val.submatrix id c = 1 := by
      have := Matrix.submatrix_mul_equiv ((β' * U)⁻¹).val (β' * U).val c (Equiv.refl m) c
      rw [Units.inv_mul, Matrix.submatrix_one_equiv] at this
      exact this
    rw [hj2, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _), h1, Matrix.one_mul, Units.mul_inv]
  · have h1 : j.mulVec x = (β' * U).val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [hj2, ← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
      rfl
    have h2 : (β'⁻¹).val.mulVec (j.mulVec x) = U.val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [h1, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [h2]
    constructor
    · intro h i
      rw [hu]
      exact mulVec_mem S u _ (fun k => h _) i
    · intro h i
      have h3 := mulVec_mem S u' _ h (c i)
      rw [← hu', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Function.comp_apply, Equiv.symm_apply_apply] at h3
      exact h3

variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}

omit [DecidableEq n] in
theorem conj_eq (h1 : J * J' = 1) (hc : M' * J = J * M) : M' = J * M * J' := by
  rw [← hc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_inv (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M * J' = J' * M' := by
  rw [conj_eq h1 hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem supp_conj (h1 : J * J' = 1) (hc : M' * J = J * M) (hs : f • (M - 1) = M - 1) : f • (M' - 1) = M' - 1 := by
  have hs2 : M' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, ← conj_eq h1 hc]
  rw [hs2, ← Matrix.smul_mul, ← Matrix.mul_smul, hs]

theorem det_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M'.det = M.det := by
  rw [conj_eq h1 hc]
  exact Matrix.det_conj_of_mul_eq_one h1 h2

variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [DecidableEq n] in
theorem lat_inv (h1 : J * J' = 1) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (y : m → R) :
    f • y ∈ L' ↔ f • J'.mulVec y ∈ L := by
  rw [hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

omit [DecidableEq n] in
theorem stab_conj (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc' : ∀ y ∈ L', f • y ∈ L') (ha : ∀ y ∈ L, f • M.mulVec y ∈ L) : ∀ y ∈ L', f • M'.mulVec y ∈ L' := by
  intro y hy
  have h3 := ha _ ((lat_inv h1 hL y).1 (loc' y hy))
  rw [hL, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← conj_eq h1 hc] at h3
  exact h3

omit [DecidableEq n] in
theorem cont_conj {p : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') (hb : ∀ y ∈ L, ∃ z ∈ L, f • p • y = f • M.mulVec z) :
    ∀ y ∈ L', ∃ z ∈ L', f • p • y = f • M'.mulVec z := by
  intro y hy
  obtain ⟨z, hz, h3⟩ := hb _ ((lat_inv h1 hL y).1 (loc' y hy))
  refine ⟨f • J.mulVec z, (hL z).1 (loc z hz), ?_⟩
  have h4 := congrArg J.mulVec h3
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hc, smul_comm p, smul_smul, hf] at h4
  rw [h4, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec]

variable {R' : Type} [CommRing R']

omit [Fintype n] in
theorem supp_map_iff (φ : R' →+* R) (g : R') (A : Matrix n n R') :
    φ g • (A.map φ - 1) = A.map φ - 1 ↔ ∀ i j, φ (g * (A - 1) i j) = φ ((A - 1) i j) := by
  have h : ∀ i j, φ ((A - 1) i j) = (A.map φ - 1) i j := by
    intro i j
    rw [← Matrix.map_one φ φ.map_zero φ.map_one]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  simp only [map_mul, h]
  rw [← Matrix.ext_iff]
  rfl

omit [DecidableEq m] in
theorem map_mul_one (φ : R' →+* R) {A : Matrix n m R'} {B : Matrix m n R'} (h : A * B = 1) : A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ φ.map_zero φ.map_one]

omit [DecidableEq m] [DecidableEq n] in
theorem map_conj (φ : R' →+* R) {A : Matrix m m R'} {B : Matrix m n R'} {C : Matrix n n R'} (h : A * B = B * C) :
    A.map φ * B.map φ = B.map φ * C.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

omit [DecidableEq m] [DecidableEq n] [Fintype m] in
theorem mulVec_map_inv (φ : R' →+* R) (ψ : R →+* R') (h : ∀ x, ψ (φ x) = x) (j : Matrix m n R') (y : n → R) :
    (j.mulVec fun a => ψ (f * y a)) = fun a => ψ (f * (j.map φ).mulVec y a) := by
  funext a

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, h]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem map_mul_det (φ : R' →+* R) (e : R') (A : Matrix m m R') (B : Matrix n n R') (h : (A.map φ).det = (B.map φ).det) :
    φ (e * A.det) = φ (e * B.det) := by
  rw [map_mul, map_mul, RingHom.map_det, RingHom.map_det]
  exact congrArg (φ e * ·) h

end Abstract

variable {D : D7}

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem inf_eq {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : (mt V g).map (infPart D) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem idem_det {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {m n : ℕ} (A : Matrix (Fin m) (Fin m) (Formalism.L2.Theta.AE D))
    (B : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) (h : (A.map (finPart D)).det = (B.map (finPart D)).det) :
    e * A.det = e * B.det := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ (map_mul_det (finPart D) e A B h)
  simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]

theorem suppAt_iff (e : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppAt e V α ↔ finPart D (e + cA D e) • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) (e + cA D e) (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

theorem transfer {V V' : HSp D} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) {α : GA D V} {α' : GA D V'} (hα' : α' ∈ GfC V')
    (hc : HMul.hMul (finMat D.sp.cm.sig V'.gram α') J = HMul.hMul J (finMat D.sp.cm.sig V.gram α))
    (hL : ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D e • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D e • y ∈ Formalism.L2.NTheta.LamHat V')
    {ϖ : D.host.E} {k : ℕ} (h : Formalism.L2.NTheta.IsHeckeElt V e ϖ k α) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k α' := by
  obtain ⟨hα, hs, ha, hb, u, u', hu, hu', huu, hd⟩ := h
  have hf : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1]
  refine ⟨hα', ?_, stab_conj hf h1 hc hL loc' ha, cont_conj hf h1 hc hL loc loc' hb, u, u', hu, hu', huu, ?_⟩
  · exact (suppAt_iff e hα').2 (supp_conj h1 hc ((suppAt_iff e hα).1 hs))
  · exact (idem_det he _ _ (det_conj h1 h2 hc)).trans hd

def unswap (D : D7) : EAf D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (x) : unswap D (swapAE D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply x

theorem swap_unswap (x) : swapAE D (unswap D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).apply_symm_apply x

theorem finE_unswap (V : HSp D) (g : GA D V) : (finE V g).val.map (unswap D) = finMat D.sp.cm.sig V.gram g := by
  ext i j
  exact unswap_swap _

end GlobalTheory.HeckeTrans

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMeanSquareForm

open GlobalTheory.HeisOrtho

theorem exists_form {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (M : Submodule ℂ (X → ℂ))
    (hm : ∀ f ∈ M, Measurable f) (hb : ∀ f ∈ M, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ f g : M, B f g = ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ∧
      ∀ f : M, ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (B f f).re := by
  have hi : ∀ f g : M, Integrable (fun x => (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x)) ν := fun f g => by
    obtain ⟨C, hC⟩ := hb f f.2
    obtain ⟨C', hC'⟩ := hb g g.2
    refine Integrable.of_bound
      (((hm f f.2).mul (Complex.continuous_conj.measurable.comp (hm g g.2))).aestronglyMeasurable)
      (C * C') (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f g : M => ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ?_ ?_ ?_ ?_, fun _ _ => rfl, fun f => ?_⟩
  · intro f f' g
    rw [← integral_add (hi f g) (hi f' g)]
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  · intro c f g
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f g g'
    rw [← integral_add (hi f g) (hi f g')]
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
  · intro c f g
    rw [smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]
  · rw [LinearMap.mk₂'ₛₗ_apply]
    have h1 : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) ν := by
      refine (hi f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  intro D ψ S T hψ M hM μ 𝓕 hμ h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨B, hB, hN⟩ := exists_form (μ.restrict 𝓕) M (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨B, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hB, hB, hf, hg]
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun w => (f : WO S T → ℂ) w * (starRingEnd ℂ) ((g : WO S T → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T (ratW T S γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WO S T → ℂ) (ratW T S γ + w) * (starRingEnd ℂ) ((g : WO S T → ℂ) (ratW T S γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w u))
  show ψ (symplOH S T w u) * (f : WO S T → ℂ) (w + u) *
    (starRingEnd ℂ) (ψ (symplOH S T w u) * (g : WO S T → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  first | exact @GlobalTheory.SplitIndex.not_dvd_relIndex | exact GlobalTheory.SplitIndex.not_dvd_relIndex | (intros; apply GlobalTheory.SplitIndex.not_dvd_relIndex <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem exists_nonneg_const_discriminant_term_le_budget_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
      Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ hT hG
  obtain ⟨Cn, hN⟩ := J.numsL_wtsL_fam Fm hT (Formalism.L2.GlobalTheoryTheory.Places.dlSize eps Fm)
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨CG, x1, hG⟩ := hG
  refine ⟨4 * max CG 0, max x0 x1, by positivity, fun x hx _ i => ?_⟩
  exact J.gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hN x (le_trans (le_max_left _ _) hx) i).1
      (J.factDGam_mono (hG x (le_trans (le_max_right _ _) hx) i) (le_max_left _ _))

end GlobalTheory
end
