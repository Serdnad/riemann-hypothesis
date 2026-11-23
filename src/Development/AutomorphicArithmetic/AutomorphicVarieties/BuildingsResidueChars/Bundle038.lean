module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Analysis.Complex.Circle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle030
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.V.T.UnipCard

private def upMat (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

private theorem upMat_lower (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i j : Fin n) (h : j < i) :
    upMat R n f i j = 0 := by
  simp [upMat, not_lt.2 h.le, h.ne']

private theorem upMat_diag (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) (i : Fin n) :
    upMat R n f i i = 1 := by
  simp [upMat]

private theorem upMat_det (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : (upMat R n f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => upMat_lower R n f i j h)]
  simp [upMat_diag]

private noncomputable def upGL (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) : GL (Fin n) R :=
  Matrix.nonsingInvUnit (upMat R n f) (by rw [upMat_det]; exact isUnit_one)

private theorem upGL_val (R : Type) [CommRing R] (n : ℕ)
    (f : {p : Fin n × Fin n // p.1 < p.2} → R) :
    (upGL R n f : Matrix (Fin n) (Fin n) R) = upMat R n f := rfl

private noncomputable def unipEquiv (R : Type) [CommRing R] (n : ℕ) :
    unipB R (Fin n) ≃ ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun g := fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2
  invFun f := ⟨upGL R n f, (mem_unipB R).2 ⟨fun i j h => by
      rw [upGL_val]; exact upMat_lower R n f i j h, fun i => by
      rw [upGL_val]; exact upMat_diag R n f i⟩⟩
  left_inv g := by
    obtain ⟨hl, hd⟩ := (mem_unipB R).1 g.2
    apply Subtype.ext
    apply Units.ext
    funext i j
    show ((upGL R n (fun p => ((g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) : GL (Fin n) R) :
      Matrix (Fin n) (Fin n) R) i j = _
    rw [upGL_val]
    rcases lt_trichotomy i j with h | h | h
    · simp [upMat, h]
    · subst h
      simp [upMat, hd]
    · have h1 : ¬ i < j := not_lt.2 h.le
      have h2 : i ≠ j := h.ne'
      simp [upMat, h1, h2, hl i j h]
  right_inv f := by
    funext p
    show upMat R n f p.1.1 p.1.2 = f p
    have h : p.1.1 < p.1.2 := p.2
    simp [upMat, h]

end UpperTheory.V.T.UnipCard

theorem UpperTheory.card_unipotent_upper_eq_pow :
    ∀ (R : Type) [CommRing R] [Finite R] (n : ℕ), ∃ j : ℕ, Nat.card (unipB R (Fin n)) = Nat.card R ^ j := by
  intro R _ _ n
  refine ⟨Nat.card {p : Fin n × Fin n // p.1 < p.2}, ?_⟩
  rw [Nat.card_congr (UpperTheory.V.T.UnipCard.unipEquiv R n), Nat.card_fun]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

theorem UpperTheory.unipotent_upper_map_surjective :
    ∀ {S R : Type} [CommRing S] [CommRing R] (f : S →+* R), Function.Surjective f → ∀ (n : ℕ) (x : GL (Fin n) R), x ∈ unipB R (Fin n) →
        ∃ y ∈ unipB S (Fin n), GeneralLinearGroup.map (n := Fin n) f y = x := by
  intro S R _ _ f hf n x hx
  obtain ⟨hlow, hdiag⟩ := (mem_unipB R).1 hx
  let A : Matrix (Fin n) (Fin n) S := fun i j =>
    if i < j then Function.surjInv hf ((x : Matrix (Fin n) (Fin n) R) i j) else if i = j then 1 else 0
  have hA : A.BlockTriangular id := by
    intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [A, h1, h2]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    exact Finset.prod_eq_one fun i _ => by simp [A]
  have hunit : IsUnit A.det := by simp [hdet, isUnit_one]
  have hcoe : ((GeneralLinearGroup.mk'' A hunit : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = A := rfl
  refine ⟨GeneralLinearGroup.mk'' A hunit, (mem_unipB S).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [hcoe]
    exact hA hji
  · rw [hcoe]
    simp [A]
  · apply Units.ext
    ext i j
    have hmap : ((GeneralLinearGroup.map (n := Fin n) f (GeneralLinearGroup.mk'' A hunit) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = f (A i j) := rfl
    rw [hmap]
    rcases lt_trichotomy i j with h | h | h
    · simp only [A, if_pos h]
      exact Function.surjInv_eq hf _
    · subst h
      simp [A, hdiag]
    · have h1 : ¬ i < j := not_lt.2 (le_of_lt h)
      have h2 : i ≠ j := ne_of_gt h
      simp [A, h1, h2, hlow i j h]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.UnipChar

variable {F : Type} [Field F] {n : ℕ}

private abbrev SD (n : ℕ) := {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1}

private theorem SD.ne (p : SD n) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp := p.2
  rw [h] at hp
  omega

private theorem super_mul {x y : Matrix (Fin n) (Fin n) F}
    (hx : ∀ i j, j < i → x i j = 0) (hx1 : ∀ i, x i i = 1)
    (hy : ∀ i j, j < i → y i j = 0) (hy1 : ∀ i, y i i = 1)
    {i j : Fin n} (h : (j : ℕ) = i + 1) : (x * y) i j = x i j + y i j := by
  rw [Matrix.mul_apply]
  have hij : i ≠ j := by
    intro e
    rw [e] at h
    omega
  rw [Fintype.sum_eq_add i j hij]
  · rw [hx1, hy1, one_mul, mul_one, add_comm]
  · rintro k ⟨hki, hkj⟩
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hx i k hk, zero_mul]
    · have h1 := Fin.lt_iff_val_lt_val.mp hk
      have h2 : (k : ℕ) ≠ j := fun e => hkj (Fin.ext e)
      have hjk : j < k := Fin.lt_iff_val_lt_val.mpr (by omega)
      rw [hy k j hjk, mul_zero]

private def sup (f : SD n → Fˣ) (x : Matrix (Fin n) (Fin n) F) : F :=
  ∑ p, (f p : F) * x p.1.1 p.1.2

private theorem sup_one (f : SD n → Fˣ) : sup f (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  unfold sup
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.one_apply_ne (SD.ne p), mul_zero]

private theorem sup_mul (f : SD n → Fˣ) {x y : GL (Fin n) F}
    (hx : x ∈ unipB F (Fin n)) (hy : y ∈ unipB F (Fin n)) :
    sup f ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      sup f (x : Matrix (Fin n) (Fin n) F) + sup f (y : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨a, b⟩ := (mem_unipB F).1 hx
  obtain ⟨c, d⟩ := (mem_unipB F).1 hy
  unfold sup
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.val_mul, super_mul a b c d p.2, mul_add]

private noncomputable def chi (φ : AddChar F Circle) (f : SD n → Fˣ) : unipB F (Fin n) →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ)
      map_one' := by simp [sup_one]
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, sup_mul f x.2 y.2, AddChar.map_add_eq_mul, Circle.coe_mul] }

private theorem chi_apply (φ : AddChar F Circle) (f : SD n → Fˣ) (x : unipB F (Fin n)) :
    ((chi φ f x : ℂˣ) : ℂ) = (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ) := rfl

private noncomputable def tv (i j : Fin n) (h : i ≠ j) (c : F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

private theorem tv_apply (i j : Fin n) (h : i ≠ j) (c : F) (a b : Fin n) :
    ((tv i j h c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      (1 : Matrix (Fin n) (Fin n) F) a b + Matrix.single i j c a b := rfl

private theorem tv_mem (p : SD n) (c : F) : tv p.1.1 p.1.2 (SD.ne p) c ∈ unipB F (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [tv_apply, Matrix.one_apply_ne (ne_of_gt hab), Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    have h1 := p.2
    have h2 := Fin.lt_iff_val_lt_val.mp hab
    omega
  · rw [tv_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    exact SD.ne p h.symm

private theorem sup_tv (f : SD n → Fˣ) (p : SD n) (c : F) :
    sup f ((tv p.1.1 p.1.2 (SD.ne p) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = f p * c := by
  simp only [sup]
  rw [Finset.sum_eq_single p]
  · rw [tv_apply, Matrix.one_apply_ne (SD.ne p), zero_add, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro q _ hq
    rw [tv_apply, Matrix.one_apply_ne (SD.ne q), zero_add, Matrix.single_apply, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    exact hq (Subtype.ext (Prod.ext h1.symm h2.symm))
  · intro h
    exact absurd (Finset.mem_univ p) h

private theorem chi_inj (φ : AddChar F Circle) (hφ : φ ≠ 1) :
    Function.Injective (chi (n := n) φ) := by
  intro f g hfg
  funext p
  by_contra hne
  apply hφ
  ext a
  have hd : ((f p : F) - g p) ≠ 0 := sub_ne_zero.mpr (fun e => hne (Units.ext e))
  have key := congrArg (fun χ => ((χ ⟨tv p.1.1 p.1.2 (SD.ne p) (((f p : F) - g p)⁻¹ * a), tv_mem p _⟩ : ℂˣ) : ℂ)) hfg
  simp only [chi_apply, sup_tv] at key
  have key' : φ ((f p : F) * (((f p : F) - g p)⁻¹ * a)) = φ ((g p : F) * (((f p : F) - g p)⁻¹ * a)) :=
    Circle.coe_injective key
  have ha : a = (f p : F) * (((f p : F) - g p)⁻¹ * a) - g p * (((f p : F) - g p)⁻¹ * a) := by
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [AddChar.one_apply, ha, AddChar.map_sub_eq_div, key', div_self']

private noncomputable def psi (φ : AddChar F Circle) : AddChar F ℂ where
  toFun a := (φ a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_prim {φ : AddChar F Circle} (hφ : φ ≠ 1) : (psi φ).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h
  apply hφ
  ext a
  have e := congrArg (fun ψ : AddChar F ℂ => ψ a) h
  simp only [AddChar.one_apply] at e ⊢
  exact e.trans Circle.coe_one.symm

private theorem sum_units_eq [Fintype F] [DecidableEq F] (h : F → ℂ) :
    ∑ a : Fˣ, h a = ∑ a : F, h a - h 0 := by
  rw [← Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    Finset.sum_subtype (Finset.univ.erase 0) (p := fun a => a ≠ 0) (fun a => by simp)]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

private theorem sum_units_psi [Fintype F] [DecidableEq F] {φ : AddChar F Circle} (hφ : φ ≠ 1) (b : F) :
    ∑ a : Fˣ, psi φ (-((a : F) * b)) =
      (((Fintype.card F : ℤ) * (if b = 0 then 1 else 0) - 1 : ℤ) : ℂ) := by
  rw [sum_units_eq (fun a : F => psi φ (-(a * b)))]
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, ← mul_neg]
  rw [AddChar.sum_mulShift (-b) (psi_prim hφ)]
  by_cases hb : b = 0 <;> simp [hb]

private theorem psi_sum {ι : Type} (φ : AddChar F Circle) (s : Finset ι) (g : ι → F) :
    psi φ (∑ i ∈ s, g i) = ∏ i ∈ s, psi φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

private theorem chi_inv [Fintype F] [DecidableEq F] (φ : AddChar F Circle) (f : SD n → Fˣ)
    (x : unipB F (Fin n)) :
    (((chi φ f x)⁻¹ : ℂˣ) : ℂ) =
      ∏ p, psi φ (-((f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2)) := by
  rw [Units.val_inv_eq_inv_val, chi_apply, ← psi_sum, Finset.sum_neg_distrib]
  simp only [sup]
  show _ = ((φ (-_) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv]

end UpperTheory.UnipChar

open UpperTheory.UnipChar in
theorem UpperTheory.exists_injective_generic_unipotent_characters :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (φ : AddChar F Circle), φ ≠ 1 →
        ∃ χ : ({p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1} → Fˣ) → (unipB F (Fin n) →* ℂˣ),
          Function.Injective χ ∧
          (∀ f x, ((χ f x : ℂˣ) : ℂ) = (φ (∑ p, (f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) : ℂ)) ∧
          ∃ c : unipB F (Fin n) → ℤ, ∀ x, (c x : ℂ) = ∑ f, (((χ f x)⁻¹ : ℂˣ) : ℂ) := by
  intro F _ _ _ n φ hφ
  refine ⟨chi φ, chi_inj φ hφ, fun f x => chi_apply φ f x, ?_⟩
  refine ⟨fun x => ∏ p : SD n, ((Fintype.card F : ℤ) *
    (if ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = 0 then 1 else 0) - 1), fun x => ?_⟩
  simp only [Int.cast_prod, chi_inv]
  refine Eq.trans ?_ (Fintype.prod_sum (κ := fun _ : SD n => Fˣ)
    (fun p (a : Fˣ) => psi φ (-((a : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2))))
  exact Finset.prod_congr rfl fun p _ => (sum_units_psi hφ _).symm
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.card_padicAlgCl_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk (PadicAlgCl p) = Cardinal.continuum := by
  have hle : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum := by
    have h1 : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p)) := Cardinal.mk_quotient_le
    have h2 : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_subtype_le _
    refine h1.trans (h2.trans ?_)
    rw [Cardinal.mk_arrow, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat]
    simp
  have hge : Cardinal.continuum ≤ Cardinal.mk ℚ_[p] := by
    obtain ⟨f, -, -, hf⟩ :=
      Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[p])) Set.univ_nonempty
    have := Cardinal.mk_le_of_injective hf
    simpa using this
  apply le_antisymm
  · have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    refine this.trans ?_
    exact max_le hle Cardinal.aleph0_le_continuum
  · exact hge.trans (Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective)

private theorem UpperTheory.nonempty_qbar_ringEquiv_complex (p : ℕ) [Fact p.Prime] : Nonempty (Qbar p ≃+* ℂ) := by
  have hc := UpperTheory.card_padicAlgCl_eq_continuum p
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (PadicAlgCl p)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hQ
    (by rw [hc]; exact Cardinal.aleph0_lt_continuum)
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hQ
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hc, Cardinal.mk_complex]
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  exact ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht⟩

private theorem UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots {F K : Type} [Field F] [Field K] [Algebra F K] (g : K ≃ₐ[F] K) :
    ∀ d : ℕ, d ≠ 0 → (∀ p b : ℕ, p.Prime → p ^ b ∣ d → ∀ ζ : K, ζ ^ (p ^ b) = 1 → g ζ = ζ) →
    ∀ ζ : K, ζ ^ d = 1 → g ζ = ζ := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ H ζ hζ
    exact H p n hp dvd_rfl ζ hζ
  | zero =>
    intro h
    exact absurd rfl h
  | one =>
    intro _ _ ζ hζ
    rw [pow_one] at hζ
    rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    intro hd H ζ hζ
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hA : g (ζ ^ b) = ζ ^ b :=
      iha ha0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro _ rfl))) _
        (by rw [← pow_mul, mul_comm, hζ])
    have hB : g (ζ ^ a) = ζ ^ a :=
      ihb hb0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro_left _ rfl))) _
        (by rw [← pow_mul, hζ])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero ha0 hb0)] at hζ
      exact zero_ne_one hζ
    have hbez : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      have := Nat.gcd_eq_gcd_ab a b
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact_mod_cast this
    have e : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast ζ a, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hbez,
        zpow_one]
    rw [e, map_mul, map_zpow₀, map_zpow₀, hA, hB]

theorem UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ M : ℕ, 1 ≤ M → ∀ σ : Weil h,
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) ∈ Ine (F := F) A ∧ ∀ ζ : Ω, ζ ^ M = 1 → (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) ζ = ζ := by
  intro hGAR F Ω _ _ _ _ _ w A h a ha M hM σ hv hvM
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion F) (a σ) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.mpr hv
  have hdeg : deg σ = 0 := by
    have := ha.ord_eq σ
    rw [hord] at this
    omega
  refine ⟨deg_eq_zero_iff.mp hdeg, ?_⟩
  have hnat : ∀ n : ℕ, valuation (w.adicCompletion F) (n : w.adicCompletion F) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))
  apply UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) M (by omega)
  intro p b hp hpb ζ hζ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι⟩ := UpperTheory.nonempty_qbar_ringEquiv_complex p
  have hle : valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤
      valuation (w.adicCompletion F) ((p ^ b : ℕ) : w.adicCompletion F) := by
    obtain ⟨c, hc⟩ := hpb
    refine hvM.trans ?_
    rw [hc, Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (hnat c)
  have h82 := UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le F w p ι (p ^ b) (a σ) hle
  have h78 := UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit hGAR F Ω w A h a ha p ι σ hv
  rw [← h78] at h82
  exact UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one F Ω p b (σ : _root_.Formalism.ConjugateSelfDual.G F Ω) h82 ζ hζ
end
