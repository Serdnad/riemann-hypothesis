module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Module

namespace GlobalTheory.ZH

open Module in
private lemma mulVec_column_of_orthogonal_idempotents {R J C : Type} [CommRing R] [Fintype J]
    [DecidableEq C] (e : C → Matrix J J R)
    (he : ∀ c c', e c * e c' = if c = c' then e c else 0) (d c : C) (s : J) :
    (e d).mulVec (fun j => e c j s) = if d = c then (fun j => e c j s) else 0 := by
  ext i
  have h := congrFun (congrFun (he d c) i) s
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  split_ifs with hdc
  · subst hdc; rfl
  · rfl


open Module in
theorem _root_.GlobalTheory.ZH.exists_basis_adapted_to_idempotents :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by
  intro O _ _ J C _ _ _ _ e he hsum
  classical
  let f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  let E : C → Matrix J J (IsLocalRing.ResidueField O) := fun c => f (e c)
  have hE : ∀ c c', E c * E c' = if c = c' then E c else 0 := by
    intro c c'
    simp only [E, ← map_mul, he]
    split_ifs <;> simp
  have hEsum : ∑ c, E c = 1 := by simp only [E, ← map_sum, hsum, map_one]
  let w : C → J → (J → IsLocalRing.ResidueField O) := fun c s j => E c j s
  choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)
  haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)
  let W : (Σ c, T c) → (J → IsLocalRing.ResidueField O) := fun p => w p.1 (a p.1 p.2)
  have hWli : LinearIndependent (IsLocalRing.ResidueField O) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨d, t⟩ := p
    have h1 := congrArg (Matrix.mulVecLin (E d)) hg

    simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w,
    mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)] at h1
    simp only [if_pos rfl] at h1
    exact Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t
  have hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W) := by
    rw [← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s := by
      ext j
      have := congrFun (congrFun hEsum j) s
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      simp [w, Finset.sum_apply, this, Pi.single_apply]
    rw [hs]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c)) := by
      rw [hsp c]; exact Submodule.subset_span ⟨s, rfl⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨c, t⟩, rfl⟩
  let b := Basis.mk hWli hWsp
  have hcard : Fintype.card J = Fintype.card (Σ c, T c) := by
    rw [← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O),
      Module.finrank_eq_card_basis b]
  let σ : J ≃ (Σ c, T c) := Fintype.equivOfCardEq hcard
  let M : Matrix J J O := Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)
  have hdet : IsUnit M.det := by
    rw [← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
    exact hWli.comp σ σ.injective
  refine ⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    show (fun j => e c j s) ∈ Submodule.span O _
    have hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s := by
      simpa using mulVec_column_of_orthogonal_idempotents e he c c s
    have h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    have h4 : (fun j => e c j s) =
        ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i) := by
      calc (fun j => e c j s) = (e c).mulVec (fun j => e c j s) := hfix.symm
        _ = (e c).mulVec (Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M) := by rw [← h3]
        _ = _ := by
          rw [Matrix.vecMul_eq_sum]

          simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [h4]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0 :=
      mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _
    rw [h5]
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩
    · exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩

end GlobalTheory.ZH
end

section

namespace GlobalTheory.FiniteFieldCountEstimate

theorem main (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R)
    (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'),
      Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧
      (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x : B', algebraMap R B' π * x = 0 → x = 0) ∧
      (∀ g ∈ I, ∃ b' : B', algebraMap R B' π * b' = φ g) ∧
      ∀ Q : B' → Prop, (∀ b, Q (φ b)) →
        (∀ g ∈ I, ∀ b' : B', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
  classical

  let K := FractionRing R
  let L := TensorProduct R B K
  let f : B →ₐ[R] L := Algebra.TensorProduct.includeLeft
  let iR : K →ₐ[R] L := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)
  have hfa : ∀ b, algebraMap B L b = f b := fun b => rfl
  have hK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  let u : L := iR (algebraMap R K π)⁻¹
  have hcu : algebraMap R L π * u = 1 := by
    rw [← iR.commutes π, ← map_mul, mul_inv_cancel₀ hK, map_one]

  have htfL : Module.IsTorsionFree R L := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
    calc x = iR ((algebraMap R K r)⁻¹ * algebraMap R K r) * x := by
          rw [inv_mul_cancel₀ hrK, map_one, one_mul]
      _ = iR (algebraMap R K r)⁻¹ * (r • x) := by
          rw [map_mul, iR.commutes, Algebra.smul_def, mul_assoc]
      _ = 0 := by rw [hrx, mul_zero]

  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨k, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  let t : Fin k → L := fun i => u * f (gs i)
  have hπt : ∀ i, algebraMap R L π * t i = f (gs i) := fun i => by
    simp only [t]
    rw [← mul_assoc, hcu, one_mul]

  let A : MvPolynomial (Fin k) B →ₐ[R] L := (MvPolynomial.aeval t).restrictScalars R
  let S : Subalgebra R L := A.range
  have hAC : ∀ b, A (MvPolynomial.C b) = f b := fun b => by simp [A, hfa]
  have hAX : ∀ i, A (MvPolynomial.X i) = t i := fun i => by simp [A]
  have hmemf : ∀ b, f b ∈ S := fun b => ⟨MvPolynomial.C b, hAC b⟩
  let φ : B →ₐ[R] S := f.codRestrict S hmemf
  have htfS : Module.IsTorsionFree R S :=
    Function.Injective.moduleIsTorsionFree (fun x : S => (x : L)) Subtype.val_injective (fun r x => rfl)
  have hind : ∀ Q : S → Prop, (∀ b, Q (φ b)) →
      (∀ g ∈ I, ∀ b' : S, algebraMap R S π * b' = φ g → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
    intro Q hB hI hadd hmul x
    have key : ∀ P, Q ⟨A P, P, rfl⟩ := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C b =>
        have e : (⟨A (MvPolynomial.C b), _, rfl⟩ : S) = φ b := Subtype.ext (hAC b)
        rw [e]
        exact hB b
      | add p q hp hq =>
        have e : (⟨A (p + q), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ + ⟨A q, q, rfl⟩ := Subtype.ext (map_add A p q)
        rw [e]
        exact hadd _ _ hp hq
      | mul_X p i hp =>
        have e : (⟨A (p * MvPolynomial.X i), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ * ⟨A (MvPolynomial.X i), _, rfl⟩ :=
          Subtype.ext (map_mul A _ _)
        rw [e]
        refine hmul _ _ hp (hI (gs i) (by rw [← hgs]; exact Submodule.subset_span ⟨i, rfl⟩) _ ?_)
        apply Subtype.ext
        show algebraMap R L π * A (MvPolynomial.X i) = f (gs i)
        rw [hAX]
        exact hπt i
    obtain ⟨P, hP⟩ := x.prop
    have e : x = ⟨A P, P, rfl⟩ := Subtype.ext hP.symm
    rw [e]
    exact key P
  refine ⟨↥S, inferInstance, inferInstance, φ, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩
  · have : Algebra.FiniteType R (MvPolynomial (Fin k) B) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R B) inferInstance
    exact Algebra.FiniteType.of_surjective A.rangeRestrict A.rangeRestrict_surjective
  · infer_instance
  · intro a b h
    exact hf (congrArg Subtype.val h)
  · intro b'
    refine hind (fun b' => ∃ n b, algebraMap R S π ^ n * b' = φ b) (fun b => ⟨0, b, by simp⟩)
      (fun g _ b' h => ⟨1, g, by simpa using h⟩) ?_ ?_ b'
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, algebraMap R B π ^ m * b + algebraMap R B π ^ n * c, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, ← hb, ← hc]
      ring
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, b * c, ?_⟩
      rw [map_mul, ← hb, ← hc]
      ring
  · intro x hx
    exact (Module.isTorsionFree_iff_smul_eq_zero.mp htfS π x (by rw [Algebra.smul_def]; exact hx)).resolve_left
      hπ.ne_zero
  · intro g hg
    rw [← hgs] at hg
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hg
    refine ⟨⟨A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i), _, rfl⟩, Subtype.ext ?_⟩
    show algebraMap R L π * A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) = f g

    rw [← hc, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hAC, hAX, smul_eq_mul, map_mul, ← hπt i]
    ring

end GlobalTheory.FiniteFieldCountEstimate
end

section

namespace GlobalTheory

open MvPowerSeries

theorem hasSubst_pair {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) :=
  hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simpa

theorem subst_pair_subst_X {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by
  have h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext _
  exact subst_X ha i

theorem subst_pair_subst_shear {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by
  have ha : HasSubst (![z, w] : Fin 2 → PowerSeries k) := hasSubst_pair hz hw
  have h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext s
  fin_cases s
  · exact subst_X ha 0
  · show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w
    rw [subst_add ha, subst_X ha, subst_X ha]
    rfl

theorem X_one_dvd_iff_subst_eq_zero {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by
  have ha : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) :=
    hasSubst_pair PowerSeries.constantCoeff_X (map_zero _)
  constructor
  · rintro ⟨q, rfl⟩
    rw [subst_mul ha, subst_X ha]
    exact zero_mul _
  · intro hg
    have h1 : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have h2 := subst_comp_subst_apply ha h1 g
    rw [hg, ← coe_substAlgHom h1, map_zero] at h2
    have h3 : rescale (![1, 0] : Fin 2 → k) g = 0 := by
      rw [rescale_eq_subst, h2]
      congr 1
      funext s
      fin_cases s
      · show (1 : k) • (X 0 : MvPowerSeries (Fin 2) k) = substAlgHom h1 (X ())
        rw [substAlgHom_X, one_smul]
      · show (0 : k) • (X 1 : MvPowerSeries (Fin 2) k) = substAlgHom h1 0
        rw [map_zero, zero_smul]
    rw [X_dvd_iff]
    intro m hm
    have h4 := congrArg (coeff m) h3
    rw [coeff_rescale, Finsupp.prod_fintype _ _ (by simp)] at h4
    simpa [hm] using h4

theorem subst_two_variables_identities : ∀ (k : Type) [Field k], (∀ h : MvPowerSeries (Fin 2) k, (MvPowerSeries.X 1 ∣ MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h ↔ MvPowerSeries.subst (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries k) h = 0) ∧ ∀ z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) = MvPowerSeries.subst (![z, z + w] : Fin 2 → PowerSeries k) h) ∧ ∀ x z w : PowerSeries k, PowerSeries.constantCoeff z = 0 → PowerSeries.constantCoeff w = 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = x.subst z ∧ MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)) = x.subst w := by
  intro k _
  refine ⟨fun h => ⟨?_, fun z w hz hw => subst_pair_subst_shear h hz hw⟩, fun x z w hz hw =>
    ⟨subst_pair_subst_X x 0 (hasSubst_pair hz hw), subst_pair_subst_X x 1 (hasSubst_pair hz hw)⟩⟩
  rw [X_one_dvd_iff_subst_eq_zero,
    subst_pair_subst_shear h PowerSeries.constantCoeff_X (map_zero _), add_zero]

end GlobalTheory
end
