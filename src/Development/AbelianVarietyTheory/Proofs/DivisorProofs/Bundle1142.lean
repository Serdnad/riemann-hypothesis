module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.JSW

theorem whittaker_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  intro E _ _ w n ψ hψ W hWN hWK ϖ hϖ l hl

  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)

  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := l j - l i with hm
  have hlj : l j = l i + m := by omega
  have hm1 : 1 ≤ m := by omega
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy

  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

  have hu : T x ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : GlobalTheory.Whittaker.superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp

  set D := Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
    (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i) with hD
  have hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => (ϖ : w.adicCompletion E) ^ l a := by
    rw [hD]
    ext p q
    simp [Matrix.diagonal_apply]
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hlj, pow_add]
      congr 1
      ring
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.JSW
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace TorusActRing

theorem chV_id_eq {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ : X) :
    chV (𝟙 (splitTorus (Sp k) X)) χ = charUnit (Sp k) X χ := by
  ext1
  rw [chV_val]
  simp

theorem charUnit_add' {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ ψ : X) :
    charUnit (Sp k) X (χ + ψ) = charUnit (Sp k) X χ * charUnit (Sp k) X ψ := by
  rw [← chV_id_eq, ← chV_id_eq, ← chV_id_eq, chV_add]

end TorusActRing

theorem ringHom_charEnd_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  intro k _ G _ _ E O _ act hmon h1 hmul hadd
  letI := E.addCommGroup
  have hex := fun a => GlobalTheory.TorusEndChar.main k G E (act a) (hmon a)
  choose ρ₀ hρ₀ using fun a => (hex a).exists
  have uniq : ∀ a (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      τ ≫ E.i = E.i ≫ act a → (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → σ = ρ₀ a :=
    fun a σ τ e₁ e₂ => (hex a).unique ⟨τ, e₁, e₂⟩ (hρ₀ a)
  have compχ : ∀ (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → ∀ (Z : Over (Sp k)) (s : Z ⟶ splitTorus (Sp k) E.X) χ,
      chV (s ≫ τ) χ = chV s (σ χ) :=
    fun σ τ hτ Z s χ => ((splitTorus_map_of_charHom (Sp k) E.X E.X σ).2 τ hτ).2.2 Z s χ
  have one : ρ₀ 1 = AddMonoidHom.id _ := by
    refine (uniq 1 (AddMonoidHom.id _) (𝟙 _) ?_ (fun χ => ?_)).symm
    swap
    · rw [AddMonoidHom.id_apply]; exact TorusActRing.chV_id_eq E.X χ
    rw [h1, Category.id_comp, Category.comp_id]
  have mul : ∀ a b, ρ₀ (a * b) = (ρ₀ a).comp (ρ₀ b) := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    refine (uniq (a * b) _ (τa ≫ τb) ?_ ?_).symm
    · rw [Category.assoc, hb1, ← Category.assoc, ha1, Category.assoc, hmul]
    · intro χ
      rw [compχ _ τb hb2, ha2]
      rfl
  have add : ∀ a b, ρ₀ (a + b) = ρ₀ a + ρ₀ b := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    haveI := E.i_hom
    refine (uniq (a + b) _ (τa * τb) ?_ ?_).symm
    · rw [MonObj.mul_comp, ha1, hb1, hadd, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]
    · intro χ
      rw [chV_mul, ha2, hb2, AddMonoidHom.add_apply, TorusActRing.charUnit_add']
  have zero : ρ₀ 0 = 0 := by
    have := add 0 0
    rw [add_zero] at this
    simpa using this
  refine ⟨{ toFun := fun a => (ρ₀ a).toIntLinearMap
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a => ?_⟩
  · ext x; simp [one]
  · intro a b; ext x; simp [mul]
  · ext x; simp [zero]
  · intro a b; ext x; simp [add]
  · obtain ⟨τ, e₁, e₂⟩ := hρ₀ a
    exact ⟨τ, e₁, fun χ => e₂ χ⟩

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
section
attribute [local instance] Over.cartesianMonoidalCategory
namespace TorusTangent

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

def epsUnit (a : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr a
  inv := 1 - TrivSqZeroExt.inr a
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem epsUnit_add (a b : k) : epsUnit (a + b) = epsUnit a * epsUnit b := by
  ext <;> simp [epsUnit, add_comm]

theorem natur {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) := by
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  exact (congrArg (fun g => g.hom x) this).symm

noncomputable def phi (l : X →+ k) : Multiplicative X →* Γ((epsPt (𝟙 (Sp k))).left, ⊤)ˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom.toMonoidHom).comp
    { toFun := fun χ => epsUnit (l χ.toAdd)
      map_one' := by ext <;> simp [epsUnit]
      map_mul' := fun a b => by rw [toAdd_mul, map_add (f := _), epsUnit_add] }

noncomputable def tanPt (l : X →+ k) : epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X :=
  (splitTorusPointsEquiv (Sp k) X (epsPt (𝟙 (Sp k)))).symm (phi l)

theorem chV_tanPt (l : X →+ k) (χ : X) :
    (chV (tanPt l) χ).val = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
      (1 + TrivSqZeroExt.inr (l χ)) := by
  show ((splitTorusPointsEquiv _ _ _) ((splitTorusPointsEquiv _ _ _).symm (phi l))
    (Multiplicative.ofAdd χ)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem chV_comp {Z Z' : Over (Sp k)} (j : Z' ⟶ Z) (t : Z ⟶ splitTorus (Sp k) X) (χ : X) :
    (chV (j ≫ t) χ).val = j.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem ext_val {Z : Over (Sp k)} {a b : Z ⟶ splitTorus (Sp k) X}
    (h : ∀ χ, (chV a χ).val = (chV b χ).val) : a = b :=
  TorusOfCharMap.ext_chV fun χ => Units.ext (h χ)

end TorusTangent
end


open TorusTangent in
theorem splitTorus_tangent_addHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  intro k _ X _
  have hΓ := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm.injective
  refine ⟨tanPt, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    ext χ
    have e := congrArg (fun t => (chV t χ).val) h
    simp only [chV_tanPt] at e
    have e2 := congrArg TrivSqZeroExt.snd (hΓ e)
    simpa using e2
  · intro l
    let j : Over.mk (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1)
    have : j ≫ tanPt l = 1 := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt]
      simp only [j, Over.homMk_left]
      rw [natur]
      simp [chV, map_one]
    exact congrArg CommaMorphism.left this
  · intro l l'
    show (splitTorusPointsEquiv _ _ _).symm _ =
      (splitTorusPointsEquiv _ _ _).symm (phi l) * (splitTorusPointsEquiv _ _ _).symm (phi l')
    rw [← map_mul]
    congr 1
    ext χ
    simp [phi, epsUnit_add]
  · intro t l
    let s : epsPt (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (epsScale t)) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change epsScale t (algebraMap k (DualNumber k) x) = algebraMap k (DualNumber k) x
        ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl])
    have : tanPt ((AddMonoidHom.mulLeft t).comp l) = s ≫ tanPt l := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt, chV_tanPt]
      simp only [s, Over.homMk_left]
      rw [natur]
      congr 1
      ext <;> simp [epsScale, mul_comm]
    rw [this]
    rfl
  · intro τ ρ hτ l
    have hm := ((splitTorus_map_of_charHom (Sp k) X X ρ).2 τ hτ).2.2
    refine ext_val fun χ => ?_
    rw [hm, chV_tanPt, chV_tanPt]
    rfl

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatNhds

open GlobalTheory.SplitScalar

variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_actO (S T : HSp D) (x : WO S T) :
    Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x := by
  have h1 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt T p.2 := (continuous_mt T).comp continuous_snd
  have h2 : Continuous fun p : GA D S × GA D T => Formalism.L2.Theta.mt S p.1⁻¹ := (continuous_mt_inv S).comp continuous_fst
  exact (h1.matrix_mul continuous_const).matrix_mul h2

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  have h : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun _ => rfl
  rw [actO, inv_one, h, h, Matrix.one_mul, Matrix.mul_one]

theorem actO_smul {S T : HSp D} (g : GA D S) (h : GA D T) (a : AE D) (x : WO S T) :
    actO S T g h (a • x) = a • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem fin_iff {S T : HSp D} {u : WO S T} : u.map (infPart D) = 0 ↔ realIdem D • u = 0 := by
  constructor
  · exact fun h => Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun h i) j)
  · intro h
    funext i j
    have h1 := congrArg (infPart D) (congrFun (congrFun h i) j)
    rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, infPart_realIdem, one_mul] at h1
    exact h1.trans (infPart D).map_zero

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  rw [fin_iff] at hu ⊢
  rw [← actO_smul, hu, actO, Matrix.mul_zero, Matrix.zero_mul]

theorem continuous_sub_const' {X G : Type} [TopologicalSpace X] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {f : X → G} (hf : Continuous f) (x : G) : Continuous fun p => f p - x :=
  hf.sub continuous_const

theorem sub_nsmul_zero {G : Type} [AddCommGroup G] (x : G) (N : ℕ) : x - x - N • (0 : G) = 0 := by
  rw [sub_self, smul_zero, sub_self]

theorem eventually_move (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (x : WO S T) (hx : x.map (infPart D) = 0) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  have hO := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT N hN
  have hc : Continuous fun p : GA D S × GA D T => actO S T p.1 p.2 x - x :=
    continuous_sub_const' (continuous_actO S T x) x
  have h1 := (hO.preimage hc).mem_nhds (x := 1) ⟨0, AddSubgroup.zero_mem _, by
    show (actO S T 1 1 x - x - N • (0 : WO S T)).map (finPart D) = 0
    rw [actO_one, sub_nsmul_zero]
    exact Matrix.ext fun _ _ => (finPart D).map_zero⟩
  filter_upwards [h1] with p hp
  obtain ⟨l, hl, e⟩ := hp
  refine ⟨l, hl, ?_⟩
  have hi : (actO S T p.1 p.2 x - x - N • l).map (infPart D) = 0 := by
    have a1 := fin_iff.1 (actO_fin p.1 p.2 hx)
    have a2 := fin_iff.1 hx
    have a3 := fin_iff.1 (latO_fin (AddSubgroup.nsmul_mem _ hl N))
    rw [fin_iff, smul_sub, smul_sub, a1, a2, a3, sub_zero, sub_zero]
  have hz : actO S T p.1 p.2 x - x - N • l = 0 :=
    Matrix.ext fun i j => adele_ext ((congrFun (congrFun hi i) j).trans (infPart D).map_zero.symm)
      ((congrFun (congrFun e i) j).trans (finPart D).map_zero.symm)
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

theorem eventually_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  rintro D S T ΛS ΛT hS hT ⟨G, hG, hGl, hgen⟩
  refine ⟨?_, eventually_move S T ΛS ΛT hS hT⟩
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) 1 one_pos
  filter_upwards [h] with p hp
  intro w hw
  refine hgen (AddSubgroup.comap (AddMonoidHom.mk' (actO S T p.1 p.2) (actO_add p.1 p.2))
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True))
    (fun α hα u hu => ?_) w hw
  obtain ⟨l, hl, e⟩ := hp u hu
  rw [AddSubgroup.mem_comap, AddMonoidHom.mk'_apply, actO_smul, e]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _
    (AddSubgroup.add_mem _ (hGl u hu) (AddSubgroup.nsmul_mem _ hl 1))
  exact AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩

end GlobalTheory.LatNhds

end
end
