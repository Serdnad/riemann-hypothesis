module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle448
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem const_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem div_unif (v : Place k F) {π : F} (hπ : π ≠ 0) (h1 : ord v π = 1) {y : F}
    (hy : v.1 y < 1) : v.1 (π⁻¹ * y) ≤ 1 := by
  by_cases h0 : y = 0
  · simp [h0]
  have h2 := (le_one_iff v y h0).1 hy.le
  have h3 : ord v y ≠ 0 := fun h => hy.ne ((eq_one_iff v y h0).2 h)
  have h4 : ord v π⁻¹ = -1 := by
    have := ord_zpow v π (-1)
    rw [zpow_neg_one, h1] at this; simpa using this
  rw [le_one_iff v _ (mul_ne_zero (inv_ne_zero hπ) h0), ord_mul v _ _ (inv_ne_zero hπ) h0, h4]
  omega

theorem exists_residue (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) :
    ∃ f : F →ₗ[k] k, ∀ y, v.1 y ≤ 1 → f y = 0 → v.1 y < 1 := by
  let m : Submodule k F :=
    { carrier := {y | v.1 y < 1}
      add_mem' := fun {a b} ha hb => v.1.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        show v.1 (c • y) < 1
        rw [Algebra.smul_def, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (const_le_one v c)) hy }
  have h1 : (1 : F) ∉ m := by
    show ¬ v.1 1 < 1
    simp
  obtain ⟨f, hf, hk⟩ := Submodule.exists_le_ker_of_notMem h1
  refine ⟨f, fun y hy h0 => ?_⟩
  obtain ⟨c, hc⟩ := hres y hy
  have h2 : f (y - algebraMap k F c) = 0 := hk hc
  rw [map_sub, h0, Algebra.algebraMap_eq_smul_one, map_smul, zero_sub, neg_eq_zero, smul_eq_mul,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · simpa [h2] using hc
  · exact absurd h2 hf

theorem mulVec_int (v : Place k F) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hx : ∀ i, v.1 (x i) ≤ 1) (i : Fin n) :
    v.1 (u.mulVec x i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  exact mul_le_one' (hu i j) (hx j)

theorem exists_primitive (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by
  have hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1 := by
    intro h
    have h1 := (det_adj_int v n _ h).1
    have h2 : v.1 (a.det * a⁻¹.det) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)] at h2
    simp at h2
  push Not at hn
  obtain ⟨i0, j, hj⟩ := hn
  have hb : (fun l => a⁻¹ l j) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp only [Pi.zero_apply] at this
    rw [this] at hj
    simp at hj
  obtain ⟨i, hi, -, -, hmax⟩ := nrm_max v n _ hb
  have hvi : 1 < v.1 (a⁻¹ i j) := lt_of_lt_of_le hj (hmax i0)
  have hpos : 0 < v.1 (a⁻¹ i j) := lt_trans zero_lt_one hvi
  refine ⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hmax l
  · rw [Matrix.mulVec_smul]
    have e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j := by
      rw [← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]
    rw [inv_mul_lt_iff₀ hpos, mul_one]
    refine lt_of_le_of_lt ?_ hvi
    by_cases h : l = j <;> simp [Matrix.one_apply, h]

theorem exists_functional_inv_mulVec_integral_of_order (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) (n N : ℕ) :
    ∀ a : Matrix (Fin n) (Fin n) F, a.det ≠ 0 → (∀ i j, v.1 (a i j) ≤ 1) → ord v a.det = N →
      ∃ φ : (Fin n → F) →ₗ[k] (Fin N → k), ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 →
        ∀ i, v.1 (a⁻¹.mulVec x i) ≤ 1 := by
  induction N with
  | zero =>
    intro a hd ha hN
    have hu : Unimod v a := ⟨ha, (eq_one_iff v _ hd).2 (by simpa using hN)⟩
    exact ⟨0, fun x hx _ i => mulVec_int v _ x (unimod_mul_inv v n a a hu hu).2.1 hx i⟩
  | succ N ih =>
    intro a hd ha hN
    obtain ⟨π, hπ, hπ1⟩ := exists_unif v
    obtain ⟨f, hf⟩ := exists_residue v hres
    have hlt : v.1 a.det < 1 := lt_of_le_of_ne (det_adj_int v n a ha).1 (fun h => by
      have := (eq_one_iff v _ hd).1 h
      omega)
    obtain ⟨c, i, hci, hc, hac⟩ := exists_primitive v a hd hlt
    set T : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).updateCol i (π⁻¹ • c) with hT
    have hTd : T.det = π⁻¹ := by
      rw [hT, ← Matrix.cramer_apply, Matrix.cramer_one]; simp [hci]
    have h4 : ord v π⁻¹ = -1 := by
      have := ord_zpow v π (-1)
      rw [zpow_neg_one, hπ1] at this; simpa using this
    have hd' : (a * T).det ≠ 0 := by
      rw [Matrix.det_mul, hTd]; exact mul_ne_zero hd (inv_ne_zero hπ)
    have ha' : ∀ l j, v.1 ((a * T) l j) ≤ 1 := by
      intro l j
      by_cases h : j = i
      · have e : (a * T) l j = π⁻¹ * a.mulVec c l := by
          subst h
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_self, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]; exact div_unif v hπ hπ1 (hac l)
      · have e : (a * T) l j = a l j := by
          conv_rhs => rw [← Matrix.mul_one a]
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_ne h]
        rw [e]; exact ha l j
    have hN' : ord v (a * T).det = N := by
      rw [Matrix.det_mul, hTd, ord_mul v _ _ hd (inv_ne_zero hπ), hN, h4]; push_cast; ring
    obtain ⟨φ, hφ⟩ := ih (a * T) hd' ha' hN'
    let ψ : (Fin n → F) →ₗ[k] k :=
      f ∘ₗ (LinearMap.proj i) ∘ₗ ((Matrix.mulVecLin (a * T)⁻¹).restrictScalars k)
    refine ⟨LinearMap.pi fun j => Fin.cases ψ (fun j => (LinearMap.proj j) ∘ₗ φ) j,
      fun x hx h0 l => ?_⟩
    have h1 : φ x = 0 := funext fun j => by simpa using congrFun h0 j.succ
    have h2 : f ((a * T)⁻¹.mulVec x i) = 0 := by simpa [ψ] using congrFun h0 0
    have hy := hφ x hx h1
    have hyi := div_unif v hπ hπ1 (hf _ (hy i) h2)
    have e : a⁻¹ = T * (a * T)⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.2 (hTd ▸ inv_ne_zero hπ)), Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec]
    generalize (a * T)⁻¹.mulVec x = y at hy hyi
    simp only [Matrix.mulVec, dotProduct]
    apply Valuation.map_sum_le
    intro j _
    by_cases h : j = i
    · subst h
      have e2 : T l j * y j = c l * (π⁻¹ * y j) := by
        simp only [hT, Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2, map_mul]
      exact mul_le_one' (hc l) hyi
    · rw [map_mul]
      refine mul_le_one' ?_ (hy j)
      simp only [hT, Matrix.updateCol_ne h]
      by_cases h' : l = j <;> simp [Matrix.one_apply, h']

end GlobalTheory.Nef.LocalIndex


open GlobalTheory.Nef.OrdCalc GlobalTheory.Nef.LocalIndex in
theorem GlobalTheory.Nef.local_index : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  intro k F _ _ _ _ _ hF v n h hd hi
  have e : h⁻¹.det = h.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hd' : h⁻¹.det ≠ 0 := e ▸ inv_ne_zero hd
  have h0 := (le_one_iff v _ hd').1 (det_adj_int v n _ hi).1
  have h1 : ord v h⁻¹.det = -ord v h.det := by
    have := ord_zpow v h.det (-1)
    rw [zpow_neg_one] at this; rw [e, this]; ring
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨φ, hφ⟩ := exists_functional_inv_mulVec_integral_of_order v (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hF v).2 n N h⁻¹ hd' hi hN
  rw [Matrix.nonsing_inv_nonsing_inv h (isUnit_iff_ne_zero.2 hd)] at hφ
  exact ⟨N, φ, by rw [← hN, h1], hφ⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSmooth

abbrev sr (Ω : Type) [Field Ω] (s : Finset Ω) : Subring Ω := Subring.closure (s : Set Ω)

variable (Ω : Type) [Field Ω]

theorem sr_mono {s t : Finset Ω} (h : s ≤ t) : sr Ω s ≤ sr Ω t :=
  Subring.closure_mono (Finset.coe_subset.2 h)

def incl {s t : Finset Ω} (h : s ≤ t) : CommRingCat.of (sr Ω s) ⟶ CommRingCat.of (sr Ω t) :=
  CommRingCat.ofHom (Subring.inclusion (sr_mono Ω h))

theorem incl_apply {s t : Finset Ω} (h : s ≤ t) (y : sr Ω s) : ((incl Ω h).hom y : Ω) = (y : Ω) := by
  rw [incl, CommRingCat.hom_ofHom, Subring.coe_inclusion]

theorem incl_id (s : Finset Ω) : incl Ω (le_refl s) = 𝟙 _ := by
  ext x; rfl

theorem incl_comp {s t u : Finset Ω} (h : s ≤ t) (h' : t ≤ u) : incl Ω (h.trans h') = incl Ω h ≫ incl Ω h' := by
  ext x
  simp only [incl, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Subring.coe_inclusion]

theorem incl_comp_subtype {s t : Finset Ω} (h : s ≤ t) :
    incl Ω h ≫ CommRingCat.ofHom (sr Ω t).subtype = CommRingCat.ofHom (sr Ω s).subtype := by
  ext y
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
    Subring.coe_subtype, Subring.coe_subtype, incl_apply]

def diag : Finset Ω ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (sr Ω s)
  map {s t} h := incl Ω h.le
  map_id s := incl_id Ω s
  map_comp f g := incl_comp Ω f.le g.le

def cocone : Cocone (diag Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun s => CommRingCat.ofHom (sr Ω s).subtype
         naturality := fun s t h => by
           simp only [Functor.const_obj_map, Category.comp_id]
           exact incl_comp_subtype Ω h.le }

theorem cocone_ι (s : Finset Ω) : (cocone Ω).ι.app s = CommRingCat.ofHom (sr Ω s).subtype := rfl

theorem cocone_ι_apply (s : Finset Ω) (y : sr Ω s) : ((cocone Ω).ι.app s).hom y = (y : Ω) := rfl

theorem surj (x : Ω) : ∃ (s : Finset Ω) (y : sr Ω s), x = ((cocone Ω).ι.app s).hom y :=
  ⟨{x}, ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, (cocone_ι_apply Ω {x} ⟨x, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩).symm⟩

theorem inj [DecidableEq Ω] (i j : Finset Ω) (xi : sr Ω i) (xj : sr Ω j)
    (h : ((cocone Ω).ι.app i).hom xi = ((cocone Ω).ι.app j).hom xj) :
    ∃ (k : Finset Ω) (f : i ⟶ k) (g : j ⟶ k), ((diag Ω).map f).hom xi = ((diag Ω).map g).hom xj := by
  refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, Subtype.ext ?_⟩
  rw [cocone_ι_apply, cocone_ι_apply] at h
  change ((incl Ω (le_sup_left : i ≤ i ⊔ j)).hom xi : Ω) = ((incl Ω (le_sup_right : j ≤ i ⊔ j)).hom xj : Ω)
  rw [incl_apply, incl_apply, h]

def coconeIsColimit [DecidableEq Ω] : IsColimit (cocone Ω) := by
  haveI : ReflectsColimitsOfShape (Finset Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone Ω)) ?_ ?_)
  · intro x
    exact surj Ω x
  · intro i j xi xj h
    exact inj Ω i j xi xj h

end GlobalTheory.EtC.GalSmooth

namespace GlobalTheory.EtC


open GalSmooth in
theorem galois_sec_isLocallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (x : Sec F (Spec (CommRingCat.of Ω))),
      IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  obtain ⟨s, y, hy⟩ := (((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).2.1 hF) (Finset Ω) (diag Ω) (cocone Ω)
    (coconeIsColimit Ω)).1 x
  have key : ∀ τ : Ω ≃ₐ[K] Ω, Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
      ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    intro τ
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫ CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  haveI : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp [one_mem])] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b (IntermediateField.subset_adjoin K _ hb)
    have h2 := congrArg τ₀ h1
    simpa [AlgEquiv.mul_apply] using h2
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype = (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [key τ, key τ₀, hc]

end GlobalTheory.EtC

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

open GlobalTheory.EtC.LerayOne in

theorem _root_.GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (x : H R (sch.obj X) F 1),
      pull R (sch.map f) F 1 x = 0 →
        ∃ s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F,
          cobd (R := R) (E := cech f) (n := 1) s = 0 ∧
            IsCls (R := R) s (pull R (cechAug f) F 1 x) := by
  intro R _ F Y X f x hx
  obtain ⟨-, hneg, hmono, ⟨w0, hex⟩, -, -⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz⟩ := (pull R (cechAug f) F 1 x).mk_surjective
  have h0 : pull R (diag f) F 1 (CohomologyClass.mk z) = 0 := by
    rw [hz, ← pull_comp, diag_aug, hx]
  have h0' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (diag f))) z (zero_add 1)) = 0 := h0
  rw [CohomologyClass.mk_eq_zero_iff] at h0'
  obtain ⟨m, hm, w, hw⟩ := h0'
  obtain rfl : m = 0 := by omega

  have hw01 : ((chains R).map (diag f)).f 0 ≫ z.1.v 0 1 (zero_add 1) =
      w.v 0 0 (add_zero 0) ≫ (res R F).d 0 1 := by
    have := Cochain.congr_v hw 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) w 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (sch.obj Y) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj Y)).d 0 1) 0,
      zero_comp, smul_zero, add_zero] at this
    rw [this]
    change _ = ((Cochain.ofHom ((chains R).map (diag f))).comp z.1 (zero_add 1)).v 0 1 (zero_add 1)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have cm0 : (chainsXIso R (sch.obj Y) 0).inv ≫ ((chains R).map (diag f)).f 0 =
      (free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv := CupSpec.chains_map (diag f) 0
  let r : (cech f).obj (op ⦋0⦌) ⟶ (sch.obj Y).obj (op ⦋0⦌) := WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0
  have hr : r ≫ (diag f).app (op ⦋0⦌) = 𝟙 _ := diag_zero f
  let y0 : (free R).obj ((cech f).obj (op ⦋0⦌)) ⟶ (res R F).X 0 :=
    (free R).map r ≫ (chainsXIso R (sch.obj Y) 0).inv ≫ w.v 0 0 (add_zero 0)
  have hA0 : (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1) = y0 ≫ (res R F).d 0 1 := by
    calc (chainsXIso R (cech f) 0).inv ≫ z.1.v 0 1 (zero_add 1)
        = (free R).map r ≫ ((free R).map ((diag f).app (op ⦋0⦌)) ≫ (chainsXIso R (cech f) 0).inv) ≫
            z.1.v 0 1 (zero_add 1) := by
          rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id, Category.id_comp]
      _ = y0 ≫ (res R F).d 0 1 := by
          rw [← cm0, Category.assoc, hw01]
          simp only [y0, Category.assoc]
  let c : Cochain ((chains R).obj (cech f)) (res R F) 0 :=
    Cochain.single (p := 0) (q := 0) ((chainsXIso R (cech f) 0).hom ≫ y0) 0
  let b : Cocycle ((chains R).obj (cech f)) (res R F) 1 := Cocycle.mk (δ 0 1 c) 2 (by norm_num) (δ_δ 0 1 2 c)
  have hb : CohomologyClass.mk b = 0 := (CohomologyClass.mk_eq_zero_iff b).2 ⟨0, zero_add 1, c, rfl⟩
  let ζ := z - b
  have hζ : CohomologyClass.mk ζ = pull R (cechAug f) F 1 x := by
    rw [CohomologyClass.mk_sub, hb, sub_zero, hz]
  have hζv : ∀ p q hpq, ζ.1.v p q hpq = z.1.v p q hpq - (δ 0 1 c).v p q hpq := fun p q hpq => by
    simp only [ζ, b, Cocycle.coe_sub, Cochain.sub_v]
    rfl
  have hζ01 : ζ.1.v 0 1 (zero_add 1) = 0 := by
    rw [hζv, δ_v 0 1 (zero_add 1) c 0 1 (zero_add 1) 0 1 (by norm_num) (by norm_num),
      (CupSpec.isZero_chains (R := R) (cech f) 1 one_pos).eq_of_tgt (((chains R).obj (cech f)).d 0 1) 0,
      zero_comp, smul_zero, add_zero, Cochain.single_v]
    rw [← cancel_epi (chainsXIso R (cech f) 0).inv, Preadditive.comp_sub, hA0, comp_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, sub_self]
  have hδζ : δ 1 2 ζ.1 = 0 := Cocycle.δ_eq_zero ζ 2
  have hB : ζ.1.v (-1) 0 (by norm_num) ≫ (res R F).d 0 1 = 0 := by
    have := Cochain.congr_v hδζ (-1) 1 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-1) 1 (by norm_num) 0 0 (by norm_num) (by norm_num), hζ01, comp_zero,
      smul_zero, add_zero, Cochain.zero_v] at this
    exact this
  let B : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ (res R F).X 0 :=
    (chainsXIso R (cech f) 1).inv ≫ ζ.1.v (-1) 0 (by norm_num)
  have hBd : B ≫ (res R F).d 0 1 = 0 := by simp only [B, Category.assoc, hB, comp_zero]
  let s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F := hex.lift B hBd
  have hs : s ≫ resι R F = B := hex.lift_f B hBd
  refine ⟨s, ?_, ζ, hζ, ?_⟩
  · have h20 := Cochain.congr_v hδζ (-2) 0 (by norm_num)
    rw [δ_v 1 2 (by norm_num) ζ.1 (-2) 0 (by norm_num) (-1) (-1) (by norm_num) (by norm_num),
      (hneg (-1) (by norm_num)).eq_of_tgt (ζ.1.v (-2) (-1) (by norm_num)) 0, zero_comp, zero_add, Cochain.zero_v] at h20
    have h2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
    rw [h2, one_smul] at h20
    have hd : (chainsXIso R (cech f) 2).inv ≫ ((chains R).obj (cech f)).d (-2) (-1) =
        (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (free R).map ((cech f).δ i)) ≫ (chainsXIso R (cech f) 1).inv :=
      CupSpec.chains_d (cech f) 1
    have h3 := congrArg ((chainsXIso R (cech f) 2).inv ≫ ·) h20
    simp only [comp_zero] at h3
    rw [← Category.assoc, hd, Category.assoc] at h3
    apply (cancel_mono (resι R F)).1
    rw [zero_comp, cobd, Preadditive.sum_comp]
    rw [Preadditive.sum_comp] at h3
    refine Eq.trans ?_ h3
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Preadditive.zsmul_comp, Category.assoc, hs, B]
  · apply Cochain.ext
    intro p q hpq
    by_cases hp1 : p = -((1 : ℕ) : ℤ)
    · subst hp1
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hs]
      change _ = (chainsXIso R (cech f) 1).hom ≫ (chainsXIso R (cech f) 1).inv ≫ ζ.1.v _ 0 hpq
      rw [Iso.hom_inv_id_assoc]
    · rw [Cochain.single_v_eq_zero _ _ _ _ _ hp1]
      by_cases hp0 : p = 0
      · subst hp0
        obtain rfl : q = 1 := by omega
        exact hζ01
      · by_cases hpos : 0 < p
        · exact (CupSpec.isZero_chains (cech f) p hpos).eq_of_src _ _
        · exact (hneg q (by omega)).eq_of_tgt _ _
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent : ∀ (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (C D : T ⥤ AbCx) (φ : C ⟶ D), (∃ b : ℤ, ∀ n : ℤ, n < b → ∀ U, IsZero ((C.obj U).X n) ∧ IsZero ((D.obj U).X n)) → Refines Cov (fun U X a => ∀ n, WExact (term C n) a ∧ WExact (term D n) a) → LocSurj Cov φ → LocInj Cov φ → ∀ U, SurjH (φ.app U) ∧ InjH (φ.app U) := by
  first | (exact @GlobalTheory.CartanOne.cartan_one) | (exact GlobalTheory.CartanOne.cartan_one) | (intros; apply GlobalTheory.CartanOne.cartan_one <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_log_twist_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  first | exact @GlobalTheory.OTY.exists_log_twist | exact GlobalTheory.OTY.exists_log_twist | (intros; apply GlobalTheory.OTY.exists_log_twist <;> assumption)
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i}, ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  first | (exact @GlobalTheory.PD.rA_single_polyEquiv) | (exact GlobalTheory.PD.rA_single_polyEquiv) | (intros; apply GlobalTheory.PD.rA_single_polyEquiv <;> assumption)
end
