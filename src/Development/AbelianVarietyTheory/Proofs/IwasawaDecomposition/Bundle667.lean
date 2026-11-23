module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle652
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj.PointsOfFlagModel GlobalTheory.ShFam.Pad.Pull

namespace GlobalTheory.ModelPt

theorem exists_ptC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X), Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn → ∃ P : PointsOfFlagModel.PtC (Y Z.i) C, z ≫ Z.π = P.yt := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z C z hz
  set w : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ z with hw
  obtain ⟨pt⟩ : Nonempty (Sp ↥C.S) := inferInstance
  have hpt : w pt ∈ Z.opn := hz ⟨pt, rfl⟩
  rw [← Z.cover] at hpt
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hpt
  have hsub : Subsingleton (Sp ↥C.S) := inferInstance
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 w (fun q _ => by
    rw [Subsingleton.elim q pt]; exact ha)
  have hcomp : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    rw [← Spec.map_comp]; rfl
  let fK : Z.i.c.F →+* ↥C.S := φ.comp (Z.alg a)
  let alg : ↥(Z.i.c.V W) →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.π ≫ (Y Z.i).s)).hom
  have halg : spMap alg = z ≫ Z.π ≫ (Y Z.i).s := Spec.map_preimage _
  have hs := affineOpenChart_comp_structure_eq_spMap Z hφ
  have compat : (intO ↥C.S).subtype.comp alg = fK.comp (Z.i.c.V W).subtype := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    change spMap _ = spMap _
    rw [hcomp, hcomp, halg, ← hs, hw, Category.assoc]
  have := (Y Z.i).jQ_open
  let q : Sp ↥C.S ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) (spMap fK) ((Category.assoc _ _ _).trans hs)
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have hq2 : q ≫ pullback.snd _ _ = spMap fK := pullback.lift_snd _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z hφ ⟨x, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  let y := IsOpenImmersion.lift _ q hr
  have hy : y ≫ (Y Z.i).jQ = q := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨alg, fK, compat, y, ?_, z ≫ Z.π, ?_, ?_⟩, rfl⟩
  · rw [← (Y Z.i).jQ_over, ← Category.assoc, hy, hq2]
  · rw [halg, Category.assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% hy, hq]
    rfl

end GlobalTheory.ModelPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

theorem _root_.GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  first | exact @GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | exact GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | (intros; apply GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot <;> assumption)
end

section

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM

namespace GlobalTheory.PolFan

namespace ConeMeet

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCone bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

theorem apply_sum_nsmul {L : Type} [AddCommGroup L] (F : L →ₗ[ℤ] ℤ) {p : ℕ} (n : Fin p → ℕ) (v : Fin p → L) :
    F (∑ j, n j • v j) = ∑ j, (n j : ℤ) * F (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_nsmul]

theorem ray {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    (hγ' : IsCone bar φ γ') {i : Fin m} {k : ℕ} {d : Fin m' → ℕ} (hk : 0 < k) (hkd : k • γ i = ∑ j, d j • γ' j)
    (hback : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • γ' j = ∑ l, e l • γ l) :
    ∃ j, γ i = γ' j := by
  classical
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf : ∀ a b, f a (g b) = if a = b then 1 else 0 := hf
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have H1 : k • g i = ∑ j, d j • g' j := Subtype.ext (by simpa [g, g', Submodule.coe_sum] using hkd)
  have H2 : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := hback j hj
    exact ⟨kj, e, hkj, Subtype.ext (by simpa [g, g', Submodule.coe_sum] using he)⟩

  have coord : ∀ j, d j ≠ 0 → ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ kj • g' j = ∑ l, e l • g l ∧
      ∀ l, (kj : ℤ) * f l (g' j) = e l := fun j hj => by
    obtain ⟨kj, e, hkj, he⟩ := H2 j hj
    refine ⟨kj, e, hkj, he, fun l => ?_⟩
    have t := congrArg (f l) he
    rw [map_nsmul, apply_sum_nsmul] at t
    simpa [hf] using t
  have Z : ∀ l, l ≠ i → ∀ j, d j ≠ 0 → f l (g' j) = 0 := by
    intro l hl
    have s := congrArg (f l) H1
    rw [map_nsmul, apply_sum_nsmul, hf, if_neg hl, smul_zero] at s
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (d j : ℤ) * f l (g' j) := fun j _ => by
      by_cases hd : d j = 0
      · simp [hd]
      · obtain ⟨kj, e, hkj, -, he⟩ := coord j hd
        have : 0 ≤ (kj : ℤ) * f l (g' j) := (he l).symm ▸ Int.natCast_nonneg _
        exact mul_nonneg (Int.natCast_nonneg _) ((mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 this)
    intro j hd
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 s.symm j (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : k • g i = 0 := by rw [H1]; simp [hc]
    have s := congrArg (f i) this
    rw [map_nsmul, hf, if_pos rfl, map_zero] at s
    simp at s
    omega
  obtain ⟨kj, e, hkj, he, hc⟩ := coord j hj
  have hel : ∀ l, l ≠ i → e l = 0 := fun l hl => by
    have := hc l
    rw [Z l hl j hj, mul_zero] at this
    exact_mod_cast this.symm
  have he' : kj • g' j = e i • g i := by
    rw [he, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  have t := congrArg (f' j) he'
  rw [map_nsmul, map_nsmul, hf', if_pos rfl] at t
  simp only [nsmul_eq_mul, mul_one] at t
  have hx := hc i
  have hx0 : 0 ≤ f i (g' j) := (mul_nonneg_iff_of_pos_left (by exact_mod_cast hkj)).1 (hx ▸ Int.natCast_nonneg _)
  have hxy : f i (g' j) * f' j (g i) = 1 := by
    have : (kj : ℤ) * (f i (g' j) * f' j (g i)) = kj * 1 := by
      rw [← mul_assoc, hx, mul_one]; exact_mod_cast t.symm
    exact mul_left_cancel₀ (by exact_mod_cast hkj.ne') this
  have hx1 : f i (g' j) = 1 := Int.eq_one_of_mul_eq_one_right hx0 hxy
  have hei : e i = kj := by rw [hx1, mul_one] at hx; exact_mod_cast hx.symm
  rw [hei] at he'
  refine ⟨j, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ (congrArg Subtype.val he') a b
  simp [g, g'] at this
  rcases this with h | h
  · exact h.symm
  · omega

theorem mem_of_coeff_ne_zero {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (hγ : IsCone bar φ γ) (hγ' : IsCone bar φ γ') {c : Fin m → ℝ} {c' : Fin m' → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hc' : ∀ j, 0 ≤ c' j) (hrel : ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j)) (i : Fin m) (hi : c i ≠ 0) :
    ∃ j, γ i = γ' j := by
  classical
  obtain ⟨k, d, hk, hkd⟩ := inCone hγ' hγ.mem hγ.nonneg hc hc' ((linearOn_iff φ γ).1 hγ.linear c hc) hrel i hi
  refine ray hγ hγ' hk hkd fun j hj => ?_
  refine inCone (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hγ hγ'.mem hγ'.nonneg
    (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
    ((linearOn_iff φ γ').1 hγ'.linear _ fun j => Nat.cast_nonneg _) ?_ j (by exact_mod_cast hj)
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hkd a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
  simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  exact_mod_cast this.symm

end ConeMeet


open ConeMeet in
theorem cone_meet : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) (c' : Fin m' → ℝ), IsCone bar φ γ → IsCone bar φ γ' → (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
    ∑ i, c i • toReal (γ i) = ∑ j, c' j • toReal (γ' j) → ∀ i, c i ≠ 0 → ∃ j, γ i = γ' j ∧ c i = c' j := by
  intro O _ bar φ X _ _ _ m m' γ γ' c c' hγ hγ' hc hc' hrel i hi
  classical
  obtain ⟨j, hj⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel i hi
  refine ⟨j, hj, ?_⟩
  let g : Fin m → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let g' : Fin m' → balForms bar X := fun l => ⟨γ' l, hγ'.mem l⟩
  obtain ⟨f', hf'⟩ := hγ'.basis.exists_dual
  have hf' : ∀ a b, f' a (g' b) = if a = b then 1 else 0 := hf'
  have s := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms bar X).subtype) Subtype.val_injective (f' j)
    (β := Sum.elim g g') (c := Sum.elim c (-c')) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Submodule.subtype_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
        g, g', hrel, add_neg_cancel])
  rw [Fintype.sum_sum_type] at s
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hf', Int.cast_ite,
    Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at s
  have h1 : ∑ l, c l * (f' j (g l) : ℝ) = c i := by
    rw [Finset.sum_eq_single i]
    · have : g i = g' j := Subtype.ext hj
      rw [this, hf', if_pos rfl, Int.cast_one, mul_one]
    · intro l _ hl
      by_cases hcl : c l = 0
      · rw [hcl, zero_mul]
      · obtain ⟨p, hp⟩ := mem_of_coeff_ne_zero hγ hγ' hc hc' hrel l hcl
        have : g l = g' p := Subtype.ext hp
        rw [this, hf', if_neg, Int.cast_zero, mul_zero]
        rintro rfl
        exact hl (hγ.injective (hp.trans hj.symm))
    · simp
  linarith

end GlobalTheory.PolFan
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DefForm

variable {E : Type} [Field E] [NumberField E]

def coordForm (m : ℕ) : (Fin m → 𝓞 E) →ₗ[ℤ] (Fin m → 𝓞 E) →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun y z => ∑ k, ∑ τ : E →+* ℂ, (τ (y k : E) * conj (τ (z k : E))).re)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intro n y z; simp only [Finset.smul_sum, Pi.smul_apply]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; rw [zsmul_eq_mul, zsmul_eq_mul]; simp [mul_left_comm])

theorem sum_sum_mul_re {ι : Type} [Fintype ι] (c : ι → ℝ) (u : ι → ℂ) :
    ∑ a, ∑ b, c a * c b * (u a * conj (u b)).re = Complex.normSq (∑ a, (c a : ℂ) * u a) := by

  rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_ofReal,
    show (c a : ℂ) * u a * ((c b : ℂ) * conj (u b)) = ((c a * c b : ℝ) : ℂ) * (u a * conj (u b)) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem coordForm_mem [IsCMField E] (H : Host E) (m : ℕ) : coordForm (E := E) m ∈ realForms H.bar (Fin m → 𝓞 E) := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · simp only [coordForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  · simp only [coordForm, LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ => ?_
    push_cast
    simp only [H.bar_eq, IsCMField.complexEmbedding_complexConj, map_mul, Complex.conj_conj]
    ring_nf

theorem coordForm_posDef (m : ℕ) : IsPosDef (coordForm (E := E) m) := by
  classical
  rw [isPosDef_iff_basis (Pi.basis fun _ : Fin m => RingOfIntegers.basis E)]
  intro c hc
  have hw : ∀ k (τ : E →+* ℂ), ∑ a, (c a : ℂ) * τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) =
      ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) := by
    intro k τ
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · exact Finset.sum_congr rfl fun j _ => by simp [Pi.basis_apply]
    · intro k' _ hk'
      exact Finset.sum_eq_zero fun j _ => by simp [Pi.basis_apply, Pi.single_apply, Ne.symm hk']
    · simp
  have hsum : ∑ a, ∑ a', c a * c a' * coordForm m ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a)
      ((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a') =
      ∑ k, ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) := by
    simp_rw [← hw, ← sum_sum_mul_re]
    simp only [coordForm, LinearMap.mk₂_apply, Finset.mul_sum]
    calc _ = ∑ a, ∑ k, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ a', ∑ τ : E →+* ℂ, c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ τ : E →+* ℂ, ∑ a', c a * c a' * (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a k : 𝓞 E) : E) *
            conj (τ (((Pi.basis fun _ : Fin m => RingOfIntegers.basis E) a' k : 𝓞 E) : E))).re :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hsum]
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ τ : E →+* ℂ, Complex.normSq (∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E)) :=
    fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hc ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
  ext ⟨k, j⟩
  have h2 : ∀ τ : E →+* ℂ, ∑ j, (c ⟨k, j⟩ : ℂ) * τ (RingOfIntegers.basis E j : E) = 0 := fun τ =>
    Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1
      (h1 k (Finset.mem_univ _)) τ (Finset.mem_univ _))
  have h3 : ∑ j, (c ⟨k, j⟩ : ℂ) • canonicalEmbedding.latticeBasis E j = 0 := by
    ext τ
    simpa [canonicalEmbedding.latticeBasis_apply, integralBasis_apply, canonicalEmbedding.apply_at] using h2 τ
  have := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent _ h3 j
  simpa using this

theorem exists_posDef_realForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, B ∈ realForms H.bar X ∧ IsPosDef B := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) X
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := f) fun x => LinearMap.congr_fun hs x
  refine ⟨pullR s (coordForm m), ⟨fun y z => (coordForm_mem H m).1 _ _, fun a y z => ?_⟩, ?_⟩
  · simp only [pullR_apply, map_smul]
    exact (coordForm_mem H m).2 a _ _
  · intro n x hx c hc
    exact coordForm_posDef m n (s ∘ x) (hx.map' s.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)) c hc

end GlobalTheory.DefForm
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X] {m : ℕ}

def linW (w : (X × X) →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := w.sum fun p k => k * β p.1 p.2
  map_add' β γ := by
    simp only [LinearMap.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ => by ring

def evalW (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := w.sum fun p k => (k : ℝ) * B p.1 p.2

theorem linW_apply (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : linW w β = w.sum fun p k => k * β p.1 p.2 := rfl

theorem evalW_toReal (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : evalW w (toReal β) = linW w β := by
  simp [evalW, linW_apply, Finsupp.sum]

theorem evalW_add (w : (X × X) →₀ ℤ) (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (B + B') = evalW w B + evalW w B' := by
  simp only [evalW, LinearMap.add_apply, mul_add]
  exact Finsupp.sum_add

theorem evalW_smul (w : (X × X) →₀ ℤ) (t : ℝ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (t • B) = t * evalW w B := by
  simp only [evalW, LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

def evalWL (w : (X × X) →₀ ℤ) : (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) →ₗ[ℝ] ℝ where
  toFun := evalW w
  map_add' := evalW_add w
  map_smul' t B := evalW_smul w t B

theorem evalW_sum (w : (X × X) →₀ ℤ) (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    evalW w (∑ i, t i • toReal (u i)) = ∑ i, t i * linW w (u i) := by
  have := map_sum (evalWL w) (fun i => t i • toReal (u i)) Finset.univ
  simp only [evalWL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [evalW_smul, evalW_toReal]

def rcone (u : Fin m → LinearMap.BilinForm ℤ X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • toReal (u i)}

def StrictWith {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) [Module O X] [Module.Finite O X] (N : ℕ)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (u : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ i, (ℓ (u i) : ℝ) = N * φ.evalZ (u i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i

theorem isStrict_iff {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} [Module O X] [Module.Finite O X]
    {u : Fin m → LinearMap.BilinForm ℤ X} : IsStrict bar φ u ↔ ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧
      StrictWith bar φ N ℓ u := Iff.rfl

def kDen (N n : ℕ) (𝓜 : Finset ℕ) : ℕ := N * ∏ M ∈ 𝓜, (M + 1) ^ n

def lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) : (X × X) →₀ ℤ :=
  (D : ℤ) • ((∏ M ∈ 𝓜, ((M : ℤ) + 1) ^ n) • w +
    ∑ M ∈ 𝓜, ((N : ℤ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℤ) + 1) ^ n) • ∑ y, Finsupp.single (r (a M y), r (a M y)) 1)

end GlobalTheory.PolCell
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  first | exact @GlobalTheory.PointDer.exists_eq_fderiv | exact GlobalTheory.PointDer.exists_eq_fderiv | (intros; apply GlobalTheory.PointDer.exists_eq_fderiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  first | exact @GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | exact GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | (intros; apply GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod <;> assumption)
end
