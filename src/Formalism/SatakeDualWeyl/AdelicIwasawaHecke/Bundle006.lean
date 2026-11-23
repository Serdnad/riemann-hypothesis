module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle005
public import Formalism.SatakeDualWeyl.Bundle001
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
import Mathlib.RingTheory.Henselian
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

@[expose] public section

section

noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Tens
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

def afsplitIE (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* E ⊗[F] (FiniteAdeleRing (𝓞 F) F) where
  toFun := LinearMap.lTensor E (afsplitI v)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, afsplitI_mul]

theorem afsplitIE_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (x : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] x) = a ⊗ₜ[F] afsplitI v x := rfl

theorem afsplit_prV_tmul (w : HeightOneSpectrum (𝓞 F)) (a : E) (b : (FiniteAdeleRing (𝓞 F) F)) :
    prV (E := E) w (a ⊗ₜ[F] b) = a ⊗ₜ[F] (b w) := rfl

theorem afsplit_prV_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem afsplit_prV_IE_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v)
    (x : E ⊗[F] v.adicCompletion F) : prV (E := E) w (afsplitIE v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_ne v w h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem afsplit_sigR_IE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (afsplitIE v x) = afsplitIE v (sigR σ (v.adicCompletion F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [sigR, afsplitIE_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def afsplitEps (E : Type) [CommRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] (FiniteAdeleRing (𝓞 F) F) :=
  afsplitIE v 1

theorem afsplit_decomp (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :
    afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [afsplit_prV_tmul, afsplitIE_tmul, afsplitI_eval, he, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, mul_add]

theorem afsplit_eps_mul_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    afsplitEps E v * afsplitIE v x = afsplitIE v x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [he, afsplitIE_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← afsplitI_mul, one_mul]
  | add x y hx hy => rw [map_add (f := _), mul_add, hx, hy]

theorem afsplit_eps_idem (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v * afsplitEps E v = afsplitEps E v := by
  exact afsplit_eps_mul_IE (E := E) v 1

theorem afsplit_sigR_eps (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (afsplitEps E v) = afsplitEps E v := by
  rw [afsplitEps, afsplit_sigR_IE, map_one]

theorem afsplit_prV_eps (v : HeightOneSpectrum (𝓞 F)) : prV (E := E) v (afsplitEps E v) = 1 := by
  exact afsplit_prV_IE (E := E) v 1

theorem afsplit_prV_eps_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    prV (E := E) w (afsplitEps E v) = 0 := by
  exact afsplit_prV_IE_ne (E := E) v w h 1

theorem afsplit_prV_inclE (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := rfl

theorem afsplit_prV_comp_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (sigR σ (FiniteAdeleRing (𝓞 F) F)) = (sigR σ (v.adicCompletion F)).comp (prV (E := E) v) := by
  refine RingHom.ext fun y => ?_
  simp only [RingHom.comp_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Tens

section Inj
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem afsplit_coord_prV (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (i : Module.Free.ChooseBasisIndex F E) (w : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :
    TensorProduct.lid F (w.adicCompletion F) ((b.coord i).rTensor _ (prV (E := E) w y)) =
      (TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ y)) w := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    rw [afsplit_prV_tmul]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, afsplit_smul_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, afsplit_add_apply]

theorem afsplit_inj (y : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) (hy : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w y = 0) :
    y = 0 := by
  classical
  set b := Module.Free.chooseBasis F E
  have hc : ∀ i, TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ y) = 0 := by
    intro i
    ext w
    rw [← afsplit_coord_prV b i w y, hy w]
    simp only [map_zero]
    rfl
  have hcoord : ∀ (z : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) (i : Module.Free.ChooseBasisIndex F E),
      TensorProduct.equivFinsuppOfBasisLeft b z i = TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := (FiniteAdeleRing (𝓞 F) F)) b).injective
  rw [map_zero]
  ext i
  rw [hcoord, hc i]
  rfl

end Inj
end Formalism.UG.P
end
end

section

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_borel_iff (b : GU σ n) :
    IsBorelU b ↔ (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := Iff.rfl

theorem fSatake_borel_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') :
    IsBorelU (b * b') := by
  rw [fSatake_borel_iff] at hb hb' ⊢
  simpa only [Subgroup.coe_mul, Units.val_mul] using hb.mul hb'

theorem fSatake_borel_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  rw [fSatake_borel_iff] at hb ⊢
  haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  simpa [Matrix.coe_units_inv] using this

theorem fSatake_diag_mul {M N : Matrix (Fin n) (Fin n) L} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem fSatake_borel_diag_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  have := fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem fSatake_borel_diag_inv {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    (((b⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  rw [← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]
  simp

theorem fSatake_rev_iff (k l : Fin n) : (k : ℕ) + l + 1 = n ↔ k = l.rev := by
  have := k.isLt
  have := l.isLt
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem fSatake_cTJ (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
  · rw [show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]
    rfl
  · intro j _ hj
    rw [show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag_mat {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by
  have h := congrFun (congrFun hU i) i.rev
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev] at h
  · rw [fSatake_cTJ, Fin.rev_rev,
      show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)] at h
    exact h
  · intro l _ hl
    rw [fSatake_cTJ]
    rcases lt_or_gt_of_ne hl with h1 | h1
    · have h2 : i < l.rev := by
        simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢
        omega
      rw [hb _ _ h2, map_zero, zero_mul]
    · rw [hb l i.rev h1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 :=
  fSatake_unit_diag_mat hb b.2 i

theorem fSatake_diag_exists (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := he i.rev
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  let g : GL (Fin n) L := ⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹),
    by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)],
    by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩
  have hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i)) := by
    ext a c
    by_cases h : a = c
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply, h, Ne.symm h]
  have hg : g ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    ext i l
    rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antiJ]
    split_ifs with h
    · have hl : l = i.rev := (fSatake_rev_iff l i).1 (by omega)
      subst hl
      simp [he i]
    · simp
  exact ⟨⟨g, hg⟩, rfl, rfl⟩

end Formalism.UG.P
end
end

section

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.UG.P

section Upper

variable {L : Type} [Field L] {n : ℕ}

theorem spherical_upper_iff (b : GL (Fin n) L) :
    (∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) L) i j = 0) ↔
      (b : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

theorem spherical_diag_mul (A B : Matrix (Fin n) (Fin n) L) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)
  rcases lt_or_gt_of_ne hji with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem spherical_upper_inv (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  have : Invertible (b : Matrix (Fin n) (Fin n) L) := Units.invertible b
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem spherical_upper_mul (b c : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b * c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Units.val_mul]; exact hb.mul hc

theorem spherical_diag_ne_zero (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (i : Fin n) : (b : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hd : (b : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
    exact this.ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end Upper

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem spherical_ordV_mul (x y : v.adicCompletion F)
    (hx : x ≠ 0) (hy : y ≠ 0) : ordV F v (x * y) = ordV F v x + ordV F v y := by
  unfold ordV
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy]
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective; simp [WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem spherical_ordV_unit (x y : v.adicCompletion F) (hx : x ∈ Ov F v) (hy : y ∈ Ov F v)
    (hxy : y * x = 1) : ordV F v x = 0 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hy1 : Valued.v y ≤ 1 := hy
  have hm : Valued.v y * Valued.v x = 1 := by rw [← map_mul, hxy, map_one]
  have h1 : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v y * Valued.v x := hm.symm
      _ ≤ 1 * Valued.v x := mul_le_mul' hy1 le_rfl
      _ = Valued.v x := one_mul _
  unfold ordV
  have h0 : Valued.v x ≠ 0 := by rw [h1]; exact one_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = 1 := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, h1]; rfl
  rw [this]; rfl

theorem spherical_qV_ne_zero : (qV F v : ℂ) ≠ 0 := by
  unfold qV
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem spherical_chiDelta_mul {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b c : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id) :
    chiDelta F v α (b * c) = chiDelta F v α b * chiDelta F v α c := by
  unfold chiDelta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_mul, spherical_diag_mul _ _ hb hc i,
    spherical_ordV_mul F v _ _ (spherical_diag_ne_zero b hb i) (spherical_diag_ne_zero c hc i)]
  have hq := spherical_qV_ne_zero F v
  rw [zpow_add₀ (hα i)]
  push_cast
  rw [show (-((ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) +
      (ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ)) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      = (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
        + (-(ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      by ring, Complex.cpow_add _ _ hq]
  ring

theorem spherical_chiDelta_int {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : b ∈ GLint (Fin n) (Ov F v)) : chiDelta F v α b = 1 := by
  obtain ⟨k, rfl⟩ := hk
  unfold chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hinv := spherical_upper_inv _ hb
  have hm : ((((bc (n := Fin n) (Ov F v).subtype) k)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i *
      (((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i = 1 := by
    rw [← spherical_diag_mul _ _ hinv hb, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have h0 : ordV F v ((((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) = 0 := by
    refine spherical_ordV_unit F v _ _ ?_ ?_ hm
    · simp only [bc, Units.coe_map]
      exact ((k : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
    · rw [← map_inv (bc (n := Fin n) (Ov F v).subtype) k]
      simp only [bc, Units.coe_map]
      exact (((k⁻¹ : GL (Fin n) (Ov F v)) : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
  rw [h0]; simp

end Formalism.UG.P
end
