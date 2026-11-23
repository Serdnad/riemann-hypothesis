module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle009
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem mult_operator_shifts_twist {Λ R B M : Type} [CommRing Λ] [CommRing R] [Algebra Λ R]
    [AddCommGroup B] [Module R B] [Module Λ B] [IsScalarTower Λ R B]
    [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Flat R B] [Module.Flat Λ M] : Module.Flat Λ (TensorProduct R B M) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor R M f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective
      (LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ h1
  have h3 : ∀ x, TensorProduct.AlgebraTensorModule.assoc Λ R R B M N'
        (LinearMap.lTensor (TensorProduct R B M) f x)
      = LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)
        (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul y n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N).injective
  apply h2
  rw [← h3, ← h3, hxy]

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι] [DecidableEq ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private noncomputable def vrEnt (w : E) : (U.oddForm p q).Ext :=
  (U.oddForm p q).el (T.tr w)
    (cornerProj B (U.ep p) (U.ep q) w + cornerProj B (U.ep p) (U.ep q) (T.st w))

private noncomputable def vrRec (a b : ι) (z : (U.oddForm p q).Ext) : E :=
  if a = b then z.ev • U.ep a else if a = p then z.od.1 else T.st z.od.1

omit [DecidableEq ι] in
private theorem vrEnt_od (w : E) :
    (vrEnt U p q w).od.1 = U.ep p * w * U.ep q + U.ep p * T.st w * U.ep q := by
  simp only [mul_assoc]; rfl

omit [DecidableEq ι] in
private theorem vrEnt_ev (w : E) : (vrEnt U p q w).ev = T.tr w := rfl

omit [DecidableEq ι] in
private theorem sand (a b c d : ι) (w : E) (hw : U.ep a * w * U.ep b = w) (h : c ≠ a ∨ b ≠ d) :
    U.ep c * w * U.ep d = 0 := by
  rw [← hw]
  simp only [mul_assoc]
  rcases h with h | h
  · rw [← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]
  · rw [U.coi.ortho h, mul_zero, mul_zero, mul_zero]

omit [DecidableEq ι] in
private theorem sand_st (a b : ι) (w : E) (hw : U.ep a * w * U.ep b = w) :
    U.ep b * T.st w * U.ep a = T.st w := by
  conv_rhs => rw [← hw]
  rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]

private theorem ent_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (w : E)
    (hw : U.ep a * w * U.ep b = w) :
    ((a = b → (vrEnt U p q w).od = 0) ∧ (a ≠ b → (vrEnt U p q w).ev = 0)) ∧
      vrRec U p q a b (vrEnt U p q w) = w := by
  have hst := sand_st U a b w hw
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩
  · rw [← hab] at hw hst
    have h1 : p ≠ a ∨ a ≠ q := by
      rcases ha with h | h
      · exact Or.inr (fun h' => hpq (h.symm.trans h'))
      · exact Or.inl (fun h' => hpq (h'.trans h))
    apply Subtype.ext
    rw [vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]
    rfl
  · rw [vrEnt_ev, ← hw]
    exact (units_basic T o U).2.2.1 a b w hab
  · unfold vrRec
    split_ifs with h1 h2
    · rw [← h1] at hw
      rw [vrEnt_ev]
      conv_rhs => rw [← hw, U.corner_eq, hw]
    · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
      rw [h2, hb'] at hw hst
      rw [vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]
    · have ha' : a = q := ha.resolve_left h2
      have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
      rw [ha', hb'] at hw hst
      rw [vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]

private theorem rec_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (z : (U.oddForm p q).Ext) (hz : (a = b → z.od = 0) ∧ (a ≠ b → z.ev = 0)) :
    U.ep a * vrRec U p q a b z * U.ep b = vrRec U p q a b z ∧ vrEnt U p q (vrRec U p q a b z) = z := by
  have hid : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hmem : U.ep p * (z.od : E) * U.ep q = z.od := by
    obtain ⟨y, hy⟩ := z.od.2
    rw [← hy]
    show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)
    rw [← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]
  have hoff : U.ep p * T.st (z.od : E) * U.ep q = 0 :=
    sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)
  unfold vrRec
  split_ifs with h1 h2
  · have hod := hz.1 h1
    have hpa : U.ep p * U.ep a * U.ep q = 0 := by
      rcases ha with h | h
      · rw [h, hid, U.coi.ortho hpq]
      · rw [h, U.coi.ortho hpq, zero_mul]
    refine ⟨?_, ?_⟩
    · rw [← h1, mul_smul_comm, smul_mul_assoc, hid, hid]
    · apply Prod.ext
      · change (vrEnt U p q (z.ev • U.ep a)).ev = z.ev
        rw [vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]
      · change (vrEnt U p q (z.ev • U.ep a)).od = z.od
        apply Subtype.ext
        rw [vrEnt_od, hod, map_smul, U.st_ep]
        simp only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]
        rfl
  · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
    have hev := hz.2 h1
    rw [h2, hb']
    refine ⟨hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (z.od : E)).ev = z.ev
      rw [vrEnt_ev, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (z.od : E)).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, hmem, hoff, add_zero]
  · have ha' : a = q := ha.resolve_left h2
    have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
    have hev := hz.2 h1
    rw [ha', hb']
    refine ⟨sand_st U p q _ hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (T.st (z.od : E))).ev = z.ev
      rw [vrEnt_ev, T.tr_st, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (T.st (z.od : E))).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, T.st_st, hmem, hoff, zero_add]

end aux

theorem UpperTheory.V.AlgebraTools.vr_range :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → Function.Injective (U.vr p q) ∧ ∀ Y : Matrix ι ι (U.oddForm p q).Ext, Y ∈ Set.range (U.vr p q) ↔ ∀ i j, (o i = o j → (Y i j).od = 0) ∧ (o i ≠ o j → (Y i j).ev = 0) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hxx, -, -, -, -, hsum, hcor⟩ := units_basic T o U
  have hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j)) :=
    fun _ _ _ => rfl
  have hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j) := by
    intro w i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2
  have hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0 := by
    intro i k
    split_ifs with h
    · rw [h, U.x_st]
    · exact hxx i k h
  refine ⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩
  · rw [hsum w, hsum w']
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hrec w i j, ← hrec w' i j, h]
  · rintro ⟨w, rfl⟩ i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1
  · intro hY
    refine ⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩
    refine Matrix.ext (fun i j => ?_)
    rw [hvr]
    have hr := rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)
    have key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
        T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j) := by
      calc U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
            T.st (U.x j)
          = ∑ k, ∑ l, (U.x i * T.st (U.x k)) * vrRec U p q (o k) (o l) (Y k l) *
              (U.x l * T.st (U.x j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by
            simp [hx]
        _ = vrRec U p q (o i) (o j) (Y i j) := hr.1
    rw [key]
    exact hr.2
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_one_block :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p : ι), (∀ i, o i = p) → ∃ φ : E ≃ₐ[B] Matrix ι ι B, (∀ y i j, φ y i j = T.tr (U.x i * y * T.st (U.x j))) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = T.tr y := by
  intro B E _ _ _ T ι _ _ o U p ho
  obtain ⟨hA, hB, -, hD, hE, hF, -⟩ := units_basic T o U
  have hidem : U.ep p * U.ep p = U.ep p := (U.coi.idem p).eq
  have hte : T.tr (U.ep p) = 1 := U.tr_ep p
  have hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [U.x_st, ho]
    · exact hA i j h
  have hex : ∀ j, U.ep p * U.x j = U.x j := by
    intro j
    have h := U.x_mem j
    rw [ho] at h
    calc U.ep p * U.x j = U.ep p * (U.ep p * U.x j * U.ep j) := by rw [h]
      _ = U.ep p * U.ep p * U.x j * U.ep j := by simp only [mul_assoc]
      _ = U.x j := by rw [hidem, h]
  have hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p := by
    intro i j y
    have h := hE i j y (by rw [ho i, ho j])
    rwa [ho i] at h
  have hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b := by
    intro a b ha hb
    calc T.tr (a * b) = T.tr ((T.tr a • U.ep p) * (T.tr b • U.ep p)) := by rw [← ha, ← hb]
      _ = T.tr a * T.tr b := by rw [smul_mul_smul_comm, hidem, map_smul, hte, smul_eq_mul, mul_one]
  let f : E → Matrix ι ι B := fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))
  let g : Matrix ι ι B → E := fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)
  have hfmul : ∀ y z, f (y * z) = f y * f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply]
    calc T.tr (U.x i * (y * z) * T.st (U.x j))
        = T.tr (U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j)) := by
          rw [hB, mul_one, mul_assoc (U.x i) y z]
      _ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by

          simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact hpair _ _ (hE' i k y) (hE' k j z)
  have hfadd : ∀ y z, f (y + z) = f y + f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
  have hfsmul : ∀ (r : B) y, f (r • y) = r • f y := by
    intro r y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hf1 : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]
    split_ifs <;> simp [hte]
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [g, f, Matrix.of_apply]
    conv_rhs => rw [hF y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hE' i j y
    set c := T.tr (U.x i * y * T.st (U.x j)) with hc
    rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]
  have hfg : ∀ M, f (g M) = M := by
    intro M
    ext i j
    have hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j)) := by
      intro k l
      simp only [mul_assoc]

    simp only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]
    simp [ite_mul, mul_ite, hidem, hte, apply_ite]
  have hfst : ∀ y, f (T.st y) = (f y)ᵀ := by
    intro y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.transpose_apply]
    rw [← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have hftr : ∀ y, (f y).trace = T.tr y := by
    intro y
    simp only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]
    exact (hD y).symm
  have hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]
  let φ : E ≃ₐ[B] Matrix ι ι B := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }
  exact ⟨φ, fun y i j => rfl, hfst, hftr⟩
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem flat_regular_cotangent_extension
    (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))]
    (κ : Type) [Fintype κ] (x : κ → A) (hx : CotInd A x) :
    ∃ (s t : ℕ) (z : (κ ⊕ Fin s) ⊕ Fin t → B), (∀ k, z (Sum.inl (Sum.inl k)) = algebraMap A B (x k)) ∧
      Ideal.span (Set.range z) = maximalIdeal B ∧
      ((Fintype.card ((κ ⊕ Fin s) ⊕ Fin t) : ℕ) : WithBot ℕ∞) = ringKrullDim B := by
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  obtain ⟨s, y, -, hy, hs⟩ := cotInd_extend A κ x hx
  obtain ⟨t, w, -, hw, ht⟩ := cotInd_extend (B ⧸ I) Empty (fun e => e.elim)
    ⟨fun e => e.elim, fun _ _ e => e.elim⟩
  choose v hv using fun j => Ideal.Quotient.mk_surjective (w j)
  have hw' : Ideal.span (Set.range w) = maximalIdeal (B ⧸ I) := by
    rw [← hw, Set.Sum.elim_range, Set.range_eq_empty (ι := Empty), Set.empty_union]
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
  refine ⟨s, t, Sum.elim (fun i => algebraMap A B (Sum.elim x y i)) v, fun k => rfl, ?_, ?_⟩
  · rw [Set.Sum.elim_range, Ideal.span_union]
    have h1 : Ideal.span (Set.range fun i => algebraMap A B (Sum.elim x y i)) = I := by
      rw [hI, ← hy, Ideal.map_span, ← Set.range_comp]
      rfl
    have h2 : (Ideal.span (Set.range v)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
      rw [Ideal.map_span, ← Set.range_comp, ← hw']
      congr 2
      funext j
      exact hv j
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) (h2.trans hmap.symm)
    rw [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.2 hIle] at h3
    rw [h1, h3]
  · haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
    rw [← hI, hmap] at H
    have H' := congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) H
    simp only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at H'
    rw [H', ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B ⧸ I), ← hs, ← ht]
    simp

theorem UpperTheory.V.AlgebraTools.regular_of_flat_fibre :
    ∀ (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
      [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))],
      IsRegularLocalRing B ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x → CotInd B (fun k => algebraMap A B (x k)) := by
  intro A B _ _ _ _ _ _ _ _ _
  constructor
  · obtain ⟨s, t, z, -, hz, hc⟩ := flat_regular_cotangent_extension A B Empty (fun e => e.elim)
      ⟨fun e => e.elim, fun _ _ e => e.elim⟩
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hc, ← hz, Nat.cast_le]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le
  · intro κ _ x hx
    obtain ⟨s, t, z, hzx, hz, hc⟩ := flat_regular_cotangent_extension A B κ x hx
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal B
    rw [← hc, Nat.cast_le] at h1
    have h2 := (cotInd_of_span B _ z hz h1).comp (fun k : κ => Sum.inl (Sum.inl k))
      (Sum.inl_injective.comp Sum.inl_injective)
    have h3 : (z ∘ fun k : κ => Sum.inl (Sum.inl k)) = fun k => algebraMap A B (x k) := funext hzx
    rwa [h3] at h2
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.scal_eq :
    ∀ (R ι : Type) [CommRing R] (F : Filter ι) (I : ℕ → Ideal R) (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ (r : ι → R) (s : R), (∀ j, ∀ᶠ N in F, ∀ x : M N, (r N - s) • x ∈ (I j • ⊤ : Submodule R (M N))) →
        ∀ x : ULim F I M, ULim.scal F I M r x = s • x) ∧
      (∀ s : R, (∀ j, ∀ᶠ N in F, ∀ x : M N, s • x ∈ (I j • ⊤ : Submodule R (M N))) → ∀ x : ULim F I M, s • x = 0) ∧
      (∀ (M' : ι → Type) [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, M' i →ₗ[R] M i) (r : ι → R), (∀ i x, g i (f i x) = r i • x) →
        ∀ x : ULim F I M, ULim.map F (fun _ => le_rfl) g (ULim.map F (I' := I) (fun _ => le_rfl) f x) = ULim.scal F I M r x) := by
  intro R ι _ F I M _ _
  have hs : ∀ (r : ι → R) (p : ∀ i, M i), ULim.scal F I M r (ULim.mk F I M p) = ULim.mk F I M (fun i => r i • p i) := by
    intro r p
    simp only [ULim.scal, ULim.map_mk, LinearMap.smul_apply, LinearMap.id_apply]
  have hc : ∀ (s : R) (p : ∀ i, M i), s • ULim.mk F I M p = ULim.mk F I M (fun i => s • p i) := by
    intro s p
    rw [← map_smul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [← sub_eq_zero, hs, hc, ← map_sub, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    simpa [sub_smul] using hN (p N)
  · intro s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [hc, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    exact hN (p N)
  · intro M' _ _ f g r hfg x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [ULim.map_mk, ULim.map_mk, hs]
    simp only [hfg]
end
