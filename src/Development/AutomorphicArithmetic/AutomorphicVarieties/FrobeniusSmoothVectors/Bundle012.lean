module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.RingTheory.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrExt
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.KrullDimension.Zero

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def diagHom {H C : Type} [Group H] [CommRing C] {n : ℕ} (m : H →* Matrix (Fin n) (Fin n) C)
    (h : ∀ s, UpT (m s)) (i : Fin n) : H →* C where
  toFun s := m s i i
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [h s i b h', zero_mul]
      · rw [h t b i h', mul_zero]
    · simp

private def conjHom {H R : Type} [Group H] [Monoid R] (u : Rˣ) (m : H →* R) : H →* R where
  toFun s := (u : R) * m s * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' s t := by simp [mul_assoc]

private theorem cont_conj {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (m : X → Matrix (Fin n) (Fin n) C) (hm : ∀ i j, AdicCont I fun s => m s i j) (a b : Matrix (Fin n) (Fin n) C)
    (i j : Fin n) : AdicCont I fun s => (a * m s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * m s * b) i j)) = ∑ q, ∑ p, fun s => Ideal.Quotient.mk (I ^ N) (a i p) * Ideal.Quotient.mk (I ^ N) (m s p q) * Ideal.Quotient.mk (I ^ N) (b q j) := by
    funext s

    simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun q _ => ?_)
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun p _ => ?_)
  exact ((IsLocallyConstant.const _).mul (hm p q N)).mul (IsLocallyConstant.const _)

theorem UpperTheory.V.Fr.pr_ofbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (B : Box F n C), (B.r F.c).mat = 1 → (∀ i j, i ≠ j → ((B.r F.g0).mat - (B.r (F.star F.g0)).mat) i j = 0) → B.Cont I → ∃ ρ : NRep F n C, B.Of ρ ∧ ρ.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I B hc hdg hcont
  let rr : F.G0 →* Matrix (Fin n) (Fin n) C := (Units.coeHom _).comp (glPart F.del B.r B.nu)
  let m : ∀ v, F.Gv v →* Matrix (Fin n) (Fin n) C := fun v => conjHom (B.g v) (rr.comp (F.loc0 v))
  have hup : ∀ v s, UpT (m v s) := fun v s => B.tri v s
  let ψ : (v : F.V) → Fin n → F.Gv v →* Cˣ := fun v i => (diagHom (m v) (hup v) i).toHomUnits
  have hpol : ∀ g : F.G0, rr (F.star g) = Jmat (R := C) n * (rr g)ᵀ * Jmat (R := C) n := by
    intro g
    have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
    have hs : ((F.star g : F.G0) : F.Γ) = F.c * (↑g)⁻¹ * F.c := by
      show ((F.conj g⁻¹ : F.G0) : F.Γ) = _
      rw [Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hcc]
      rfl
    have hPl : (B.r F.c).left = 1 := Units.ext hc
    have hPr : (B.r F.c).right = -1 := by rw [B.nu, hF.del_c]
    have hX : (B.r (↑g)⁻¹).left = (glPart F.del B.r B.nu g)⁻¹ := by
      rw [← map_inv]
      rfl
    show ((B.r ↑(F.star g)).left : Matrix (Fin n) (Fin n) C) = _
    rw [hs, map_mul, map_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hPl, hPr, map_one, mul_one, one_mul, sgnAct_neg_one, hX, theta_val, inv_inv]
    rfl
  have hord : ∀ v (g : Fin n → F.Gv v), ordProd (fun s => rr (F.loc0 v s)) (fun i s => ((ψ v i s : Cˣ) : C)) g = 0 := by
    intro v g
    have hf : UpperTheory.V.W.HasFlag (rr.comp (F.loc0 v)).toHomUnits (ψ v) := ⟨B.g v, fun s => ⟨fun i j hij => hup v s i j hij, fun i => rfl⟩⟩
    exact (ord_of_flag (rr.comp (F.loc0 v)) (ψ v) hf).1 g
  refine ⟨⟨rr, ψ, hpol, fun i j hij => hdg i j hij, hord⟩, ⟨hc, fun s => rfl, fun v i s => rfl⟩, ?_, ?_⟩
  · intro i j N
    exact (hcont i j N).comp_continuous continuous_subtype_val
  · intro v i
    exact cont_conj I (fun s => (B.r (F.loc v s)).mat) (fun p q N => (hcont p q N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))) ↑(B.g v) ↑(B.g v)⁻¹ i i
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

private noncomputable def ee (F : Frame l k) (u : ℤˣ) : F.Γ := if u = 1 then 1 else F.c

private theorem ee_one : ee F 1 = 1 := if_pos rfl

private theorem ee_neg : ee F (-1) = F.c := if_neg (by decide)

private noncomputable def pr (hc : F.del F.c = -1) (s : F.Γ) : F.G0 :=
  ⟨s * ee F (F.del s), by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h | h
    · rw [h, ee_one, map_one, mul_one]
    · rw [h, ee_neg, hc]; simp⟩

private theorem pr_val (hc : F.del F.c = -1) (s : F.Γ) : (pr hc s : F.Γ) = s * ee F (F.del s) := rfl

private theorem pr_coe (hc : F.del F.c = -1) (s : F.G0) : pr hc s = s := by
  apply Subtype.ext
  have h : F.del s = 1 := s.2
  rw [pr_val, h, ee_one, mul_one]

private theorem conj_val (s : F.G0) : (F.conj s : F.Γ) = F.c * s * F.c⁻¹ := rfl

private theorem del_lc (ho : IsOpen (F.del.ker : Set F.Γ)) : IsLocallyConstant F.del := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) := ho.preimage (by fun_prop)
  filter_upwards [h1.mem_nhds (show x⁻¹ * x ∈ F.del.ker by simp)] with y hy
  have h2 : F.del (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem pr_cont (hc : F.del F.c = -1) (ho : IsOpen (F.del.ker : Set F.Γ)) : Continuous (pr hc) :=
  Continuous.subtype_mk (continuous_id.mul ((del_lc ho).comp (ee F)).continuous) _

private theorem theta_r {n : ℕ} {C : Type} [CommRing C] (ρ : NRep F n C) (g : F.G0) :
    theta (ρ.r.toHomUnits g) = ρ.r.toHomUnits (F.conj g) := by
  apply Units.ext
  rw [theta_val, ← map_inv, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, ← ρ.pol, Frame.star, inv_inv]

private noncomputable def rp (hc : F.del F.c = -1) (hs : F.c * F.c = 1) {n : ℕ} {C : Type} [CommRing C]
    (ρ : NRep F n C) : F.Γ →* GG (m := n) (R := C) where
  toFun s := ⟨ρ.r.toHomUnits (pr hc s), F.del s⟩
  map_one' := by
    have h : pr hc (1 : F.Γ) = 1 := pr_coe hc 1
    ext1
    · simp [h]
    · simp
  map_mul' s t := by
    have hi : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hs
    have hs' : ∀ x, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
    ext1
    · rw [SemidirectProduct.mul_left]
      dsimp only
      rcases Int.units_eq_one_or (F.del s) with h | h
      · rw [h, sgnAct_one, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, pr_val, pr_val, pr_val, map_mul, h, ee_one, one_mul, mul_one, mul_assoc]
      · rw [h, sgnAct_neg_one, theta_r, ← map_mul]
        congr 1
        apply Subtype.ext
        rw [Subgroup.coe_mul, conj_val, pr_val, pr_val, pr_val, map_mul, h, ee_neg, hi]
        rcases Int.units_eq_one_or (F.del t) with h' | h'
        · rw [h', mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs']
        · rw [h', neg_mul_neg, mul_one, ee_neg, ee_one]
          simp only [mul_assoc, mul_one, hs', hs]
    · simp

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_box :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (ρ : NRep F n C), ρ.Cont I → (∀ v, UpperTheory.V.W.HasFlag (ρ.r.comp (F.loc0 v)).toHomUnits (ρ.ψ v)) → ∃ B : Box F n C, B.Of ρ ∧ B.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I ρ hc hf
  choose g hg using hf
  have hm : ∀ s, (rp hF.del_c hF.c_sq ρ s).mat = ρ.r (pr hF.del_c s) := fun s => rfl
  refine ⟨⟨rp hF.del_c hF.c_sq ρ, fun s => rfl, g, fun v s i j h => ?_⟩, ⟨?_, fun s => ?_, fun v i s => ?_⟩,
    fun i j N => ?_⟩
  · have e : pr hF.del_c (F.loc v s) = F.loc0 v s := pr_coe hF.del_c (F.loc0 v s)
    rw [hm, e]
    exact (hg v s).1 i j h
  · have e : pr hF.del_c F.c = 1 := by
      apply Subtype.ext
      rw [pr_val, hF.del_c, ee_neg, hF.c_sq]
      rfl
    show (rp hF.del_c hF.c_sq ρ F.c).mat = 1
    rw [hm, e, map_one]
  · show (rp hF.del_c hF.c_sq ρ s).mat = _
    rw [hm, pr_coe]
  · exact (hg v s).2 i
  · exact (hc.1 i j N).comp_continuous (pr_cont hF.del_c hF.del_open)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O _ x = x.fst := by
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective x.fst
  have ha : (algebraMap O (DualNumber (ResidueField O)) o).fst = x.fst := by
    rw [← ho]
    first
      | rfl
      | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, IsLocalRing.ResidueField.algebraMap_eq]
  have hfst : (x - algebraMap O _ o).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, ha, sub_self]
  have hsq : (x - algebraMap O _ o) * (x - algebraMap O _ o) = 0 := by
    ext
    · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, hfst, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]
  have hmem : x - algebraMap O _ o ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h2 := hu.mul hu
    rw [hsq] at h2
    exact not_isUnit_zero h2
  have h0 := (res_eq_zero_iff O _ _).2 hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  rw [h0, ← ha]
  first
    | rfl
    | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

theorem UpperTheory.V.Fr.pr_dof :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (DualNumber (ResidueField O))] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → ∀ (ρ' : NRep F n (DualNumber (ResidueField O))) (r' : F.Γ →* GG (m := n) (R := DualNumber (ResidueField O))), ρ'.Cont (maximalIdeal _) → ρ'.bar O = ρ.bar O → (∀ s, (r' s).right = F.del s) → (r' F.c).mat = 1 → (∀ s : F.G0, (r' s).mat = ρ'.r s) → ∃ D ∈ Tan O R, ∀ s, (r' s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ R _ _ _ ρ B hU hOf ρ' r' hc' hbar hnu hatc hres
  obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hc' hbar
  have hfst : ∀ x, (g x).fst = res O R x := fun x => by
    rw [← res_dual O (g x), res_map]
  let Dd : R →ₗ[O] ResidueField O :=
    { toFun := fun x => (g x).snd
      map_add' := fun x y => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun a x => by
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
  have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = r' := by
    refine pr_ext hF _ _ _ (Box.nu _) hnu ?_ ?_
    · change (B.r F.c).mat.map g = (r' F.c).mat
      rw [hOf.atc, hatc]
      exact Matrix.map_one _ (map_zero g) (map_one g)
    · intro s
      change (B.r s).mat.map g = (r' s).mat
      rw [hOf.res]
      change (ρ.map (g : R →+* DualNumber (ResidueField O))).r s = (r' s).mat
      rw [hg, hres]
  refine ⟨Dd, ?_, fun s => ?_⟩
  · intro f h
    rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
  · rw [← hr]
    show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
    rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
    rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_sep :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P), IsNoetherianRing (lauSub P) → ⨅ N : ℕ, vertex h ^ N = ⊥ := by
  intro C K _ _ _ _ P _ h hN
  classical
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_iInf] at hp
  let comp : lauSub P → ℤ → lauSub P := fun x j =>
    ⟨AddMonoidAlgebra.single j (x.1.coeff j), single_mem_lauSub P (x.2 j)⟩
  have coeff_comp (x : lauSub P) (j : ℤ) :
      (comp x j).1 = AddMonoidAlgebra.single j (x.1.coeff j) := rfl
  have comp_mem_vertex : ∀ x : lauSub P, x ∈ vertex h → ∀ j, comp x j ∈ vertex h := by
    intro x hx j
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp x j).1.coeff 0
    rw [coeff_comp, AddMonoidAlgebra.coeff_single]
    by_cases hj : j = 0
    · subst j
      rw [Finsupp.single_eq_same]
      exact hx
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hj, map_zero]⟩
  have comp_mem_pow : ∀ (N : ℕ) (x : lauSub P), x ∈ vertex h ^ N →
      ∀ j, comp x j ∈ vertex h ^ N := by
    intro N
    induction N with
    | zero =>
      intro x hx j
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on (C := fun z => ∀ j, comp z j ∈ vertex h ^ (n + 1)) hx ?_ ?_
      · intro y hy z hz j
        have e : comp (y * z) j =
            ∑ i ∈ y.1.coeff.support, comp y i * comp z (-i + j) := by
          apply Subtype.ext
          simp only [AddSubmonoidClass.coe_finsetSum, coeff_comp, Subalgebra.coe_mul,
            AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
          rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
          exact map_sum (AddMonoidAlgebra.singleAddHom j) _ _
        rw [e, pow_succ]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (ih y hy i) (comp_mem_vertex z hz _)
      · intro y z hy hz j
        have e : comp (y + z) j = comp y j + comp z j := by
          apply Subtype.ext
          simp only [coeff_comp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
            AddMonoidAlgebra.single_add]
        rw [e]
        exact add_mem (hy j) (hz j)
  have hcomp : ∀ j : ℤ, (p : AddMonoidAlgebra K ℤ).coeff j = 0 := by
    intro j
    let a := (p : AddMonoidAlgebra K ℤ).coeff j
    let q := comp p j
    have hq : ∀ N : ℕ, q ∈ vertex h ^ N := fun N => comp_mem_pow N p (hp N) j
    have hq' : q ∈ ⨅ i : ℕ, (vertex h) ^ i • (⊤ : Submodule (lauSub P) (lauSub P)) := by
      rw [Submodule.mem_iInf]
      intro i
      simp only [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hq i
    obtain ⟨⟨r, hr⟩, hrq⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (vertex h) q).1 hq'
    have hrq' : r * q = q := hrq
    obtain ⟨c, hc, hcr⟩ := hr
    have h1 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j =
        (r : AddMonoidAlgebra K ℤ).coeff 0 * a := by
      have h0 := AddMonoidAlgebra.coeff_mul_single_add (r : AddMonoidAlgebra K ℤ) a j 0
      rw [zero_add] at h0
      exact h0
    have h2 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j = a := by
      rw [hrq']
      show (AddMonoidAlgebra.single j a).coeff j = a
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [h2, ← hcr] at h1
    have hu : IsUnit (algebraMap C K (1 - c)) :=
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c hc).map _
    have h3 : algebraMap C K (1 - c) * a = 0 := by
      rw [map_sub, map_one, sub_mul, one_mul, ← h1, sub_self]
    exact hu.mul_right_eq_zero.1 h3
  apply Subtype.ext
  ext j
  simpa using hcomp j
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem adicComplete_of_pow_eq_bot {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (h : I ^ n = ⊥) :
    IsAdicComplete I R := by
  have key : ∀ x y : R, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] → x = y := by
    intro x y hxy
    rw [h, Submodule.bot_smul] at hxy
    exact SModEq.bot.mp hxy
  refine { haus' := fun x hx => key x 0 (hx n), prec' := fun {f} hf => ⟨f n, fun m => ?_⟩ }
  rcases le_total m n with hmn | hnm
  · exact hf hmn
  · rw [key _ _ (hf hnm)]

theorem UpperTheory.V.Fr.alg_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ N : ℕ, ∃ h : IsCO O (D ⧸ 𝔪 ^ (N + 1)), @maximalIdeal _ _ h.toIsLocalRing = 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) := by
  intro O _ _ C _ _ _ D _ _ _ _ 𝔪 hV N
  have hle : 𝔪 ^ (N + 1) ≤ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hmax : 𝔪.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · intro h1
      have h1' : (1 : C) ∈ 𝔪.comap (algebraMap C D) := by
        rw [Ideal.mem_comap, map_one]
        exact h1
      rw [hV.comap] at h1'
      exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).mpr h1')
    · intro J x hJ hx hxJ
      obtain ⟨c, hc⟩ := hV.surj x
      have hcu : IsUnit c := by
        by_contra hnu
        have hcm : c ∈ maximalIdeal C := hnu
        rw [← hV.comap, Ideal.mem_comap] at hcm
        apply hx
        have := 𝔪.add_mem hc hcm
        rwa [sub_add_cancel] at this
      have hcJ : algebraMap C D c ∈ J := by
        have := J.sub_mem hxJ (hJ hc)
        rwa [sub_sub_cancel] at this
      rw [Ideal.eq_top_of_isUnit_mem J hcJ (hcu.map _)]
      exact Submodule.mem_top
  set M : Ideal (D ⧸ 𝔪 ^ (N + 1)) := 𝔪.map (Ideal.Quotient.mk (𝔪 ^ (N + 1))) with hM
  have hmem : ∀ d : D, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d ∈ M ↔ d ∈ 𝔪 :=
    fun d => Ideal.mem_quotient_iff_mem hle
  have hMmax : M.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (𝔪 ^ (N + 1)))
      Ideal.Quotient.mk_surjective hmax with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) 1 ∈ M := by
        rw [← hM] at h
        rw [h]
        exact Submodule.mem_top
      exact hmax.ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mp h1))
    · exact h
  have hMpow : M ^ (N + 1) = ⊥ := by
    rw [hM, ← Ideal.map_pow, Ideal.map_quotient_self]
  have hnil : nilradical (D ⧸ 𝔪 ^ (N + 1)) = M := by
    apply le_antisymm
    · exact nilradical_le_prime M
    · intro x hx
      refine ⟨N + 1, ?_⟩
      have := Ideal.pow_mem_pow hx (N + 1)
      rw [hMpow] at this
      exact (Submodule.mem_bot _).mp this
  haveI : (nilradical (D ⧸ 𝔪 ^ (N + 1))).IsMaximal := hnil ▸ hMmax
  haveI hloc : IsLocalRing (D ⧸ 𝔪 ^ (N + 1)) := IsLocalRing.of_isMaximal_nilradical _
  have hMeq : maximalIdeal (D ⧸ 𝔪 ^ (N + 1)) = M := (IsLocalRing.eq_maximalIdeal hMmax).symm
  have halg : ∀ a : O, algebraMap O (D ⧸ 𝔪 ^ (N + 1)) a
      = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (algebraMap O C a)) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  haveI : IsNoetherianRing D := hV.noeth
  refine ⟨@IsCO.mk O (D ⧸ 𝔪 ^ (N + 1)) _ _ _ _ hloc inferInstance ?_ ?_ ?_, hMeq⟩
  · rw [hMeq]
    exact adicComplete_of_pow_eq_bot M (N + 1) hMpow
  · refine ⟨fun a ha => ?_⟩
    have hC : IsUnit (algebraMap O C a) := by
      by_contra hnu
      have hcm : algebraMap O C a ∈ maximalIdeal C := hnu
      rw [← hV.comap, Ideal.mem_comap, ← hmem, ← halg, ← hMeq] at hcm
      exact hcm ha
    exact (IsCO.isLocalHom (O := O) (R := C)).map_nonunit a hC
  · intro x
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, hc⟩ := hV.surj d
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) c
    refine ⟨a, ?_⟩
    rw [hMeq, halg, ← map_sub, hmem]
    have hca : algebraMap C D (c - algebraMap O C a) ∈ 𝔪 := by
      rw [← Ideal.mem_comap, hV.comap]
      exact ha
    have := 𝔪.add_mem hc hca
    rwa [map_sub, sub_add_sub_cancel] at this
end
