module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

noncomputable section

open PowerSeries GlobalTheory.Cyc

namespace GlobalTheory.PrismS

theorem series_hom_ext {A B : Type} [CommRing A] [CommRing B] {f g : A⟦X⟧ →+* B⟦X⟧}
    (hC : ∀ a, f (C a) = g (C a)) (hX : f X = g X) (hd : X ∣ f X) : f = g := by
  have hp : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom :=
    Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
  ext x n
  have hx := eq_X_pow_mul_shift_add_trunc (n + 1) x
  have h1 : f (trunc (n + 1) x : A⟦X⟧) = g (trunc (n + 1) x : A⟦X⟧) := RingHom.congr_fun hp (trunc (n + 1) x)
  have h2 : X ^ (n + 1) ∣ f x - g x := by
    rw [hx, map_add (f := _), map_add (f := _), h1, add_sub_add_right_eq_sub, map_mul, map_mul, map_pow, map_pow, ← hX,
      ← mul_sub]
    exact (pow_dvd_pow_of_dvd hd _).mul_right _
  have h3 := X_pow_dvd_iff.1 h2 n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at h3

theorem C_dvd_of_map_eq_zero {A : Type} [CommRing A] (p : A) (y : A⟦X⟧)
    (h : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {p})) y = 0) : ∃ b, y = C p * b := by
  have h1 : ∀ n, ∃ c, coeff n y = p * c := fun n => by
    have := congrArg (coeff n) h
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  exact ⟨PowerSeries.mk c, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hc]⟩

section Act

variable {l : ℕ} [hl : Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ_[l] A]
  [Algebra ℤ_[l] B]

theorem act_C (c : ℤ_[l]) (a : A) : act l A c (C a) = C a := (act l A c).commutes a

theorem act_X (c : ℤ_[l]) : act l A c X = cyc l A c := (act_laws l A).1 c

theorem phi_X : phi l A X = (1 + X) ^ l - 1 := (act_X _).trans ((act_laws l A).2.2.2.1 l)

theorem map_cyc (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) : PowerSeries.map e.toRingHom (cyc l A c) = cyc l B c := by
  rw [cyc, cyc, map_sub, map_one, ← RingHom.comp_apply, ← PowerSeries.map_comp]
  congr 3
  exact RingHom.ext fun z => e.commutes z

theorem map_act (e : A →ₐ[ℤ_[l]] B) (c : ℤ_[l]) (x : A⟦X⟧) :
    PowerSeries.map e.toRingHom (act l A c x) = act l B c (PowerSeries.map e.toRingHom x) := by
  have hX : PowerSeries.map e.toRingHom (act l A c X) = cyc l B c := by rw [act_X, map_cyc]
  refine RingHom.congr_fun (series_hom_ext (f := (PowerSeries.map e.toRingHom).comp (act l A c).toRingHom)
    (g := (act l B c).toRingHom.comp (PowerSeries.map e.toRingHom)) (fun a => ?_) ?_ ?_) x
  · change PowerSeries.map e.toRingHom (act l A c (C a)) = act l B c (PowerSeries.map e.toRingHom (C a))
    rw [act_C, map_C, act_C]
  · change PowerSeries.map e.toRingHom (act l A c X) = act l B c (PowerSeries.map e.toRingHom X)
    rw [hX, map_X, act_X]
  · change X ∣ PowerSeries.map e.toRingHom (act l A c X)
    rw [hX, X_dvd_iff, cyc_const]

theorem constantCoeff_act (c : ℤ_[l]) (x : A⟦X⟧) : constantCoeff (act l A c x) = constantCoeff x := by
  obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
  have h : x = C (constantCoeff x) + X * y := by rw [← hy]; ring
  conv_lhs => rw [h, map_add (f := _), map_mul, act_C, act_X, map_add (f := _), map_mul, cyc_const]
  simp


omit hl [Algebra ℤ_[l] A] [Algebra ℤ_[l] B] in
theorem map_QQ (e : A →+* B) (s : ℕ) : PowerSeries.map e (QQ l A s) = QQ l B s := by
  simp [QQ, XX]

def phiS (σ : A →ₐ[ℤ_[l]] A) : A⟦X⟧ →+* A⟦X⟧ := (PowerSeries.map σ.toRingHom).comp (phi l A).toRingHom

theorem phiS_apply (σ : A →ₐ[ℤ_[l]] A) (x : A⟦X⟧) : phiS σ x = PowerSeries.map σ.toRingHom (phi l A x) := rfl

theorem phiS_lift (σ : A →ₐ[ℤ_[l]] A) (hu : ¬ IsUnit (l : A)) (h : ∀ a, ∃ b, σ a = a ^ l + (l : A) * b)
    (x : A⟦X⟧) : ∃ b, phiS σ x = x ^ l + (l : A⟦X⟧) * b := by
  set q := Ideal.Quotient.mk (Ideal.span {(l : A)}) with hq
  have : CharP (A ⧸ Ideal.span {(l : A)}) l := CharP.quotient A l hu
  have : CharP (A ⧸ Ideal.span {(l : A)})⟦X⟧ l := charP_of_injective_ringHom (f := C) C_injective l
  have hX : PowerSeries.map q (phiS σ X) = X ^ l := by
    rw [phiS_apply, phi_X]
    simp [add_pow_char]
  have key : (PowerSeries.map q).comp (phiS σ) = (frobenius _ l).comp (PowerSeries.map q) := by
    refine series_hom_ext (fun a => ?_) ?_ ?_
    · obtain ⟨b, hb⟩ := h a
      have h1 : phi l A (C a) = C a := act_C _ a
      rw [RingHom.comp_apply, RingHom.comp_apply, phiS_apply, h1, map_C, map_C, map_C, frobenius_def,
        ← map_pow]
      change C (q (σ a)) = _
      rw [hb, map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero (A ⧸ Ideal.span {(l : A)}) l, zero_mul, add_zero,
        map_pow]
    · rw [RingHom.comp_apply, RingHom.comp_apply, hX, map_X, frobenius_def]
    · rw [RingHom.comp_apply, hX]; exact dvd_pow_self _ hl.out.ne_zero
  obtain ⟨b, hb⟩ := C_dvd_of_map_eq_zero (l : A) (phiS σ x - x ^ l) (by
    have h2 := RingHom.congr_fun key x
    rw [RingHom.comp_apply, RingHom.comp_apply, frobenius_def] at h2
    rw [map_sub, map_pow, ← hq, h2, sub_self])
  exact ⟨b, by rw [map_natCast] at hb; rw [← hb]; ring⟩

end Act

theorem ker_eq_span {A B : Type} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] (f : A⟦X⟧ →+* B) (Q b : A⟦X⟧) (d : ℕ) (p : A) (hp : ¬ IsUnit p) (hQ : Q = X ^ d + C p * b)
    (h0 : f Q = 0) (h : ∀ r : Polynomial A, r.natDegree < d → f r = 0 → r = 0) :
    RingHom.ker f = Ideal.span {Q} := by
  refine le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 h0)
  have h1 : Q.map (IsLocalRing.residue A) = X ^ d := by
    rw [hQ, map_add (f := _), map_mul, map_C, (IsLocalRing.residue_eq_zero_iff p).2 hp]
    simp
  obtain ⟨q, r, hr⟩ := exists_isWeierstrassDivision x (g := Q) (by rw [h1]; exact pow_ne_zero _ X_ne_zero)
  have h2 : r.degree < d := by
    have := hr.degree_lt
    change r.degree < ((Q.map (IsLocalRing.residue A)).order.toNat : ℕ) at this
    rwa [h1, order_X_pow, ENat.toNat_natCast] at this
  have h3 : r = 0 := by
    by_contra hne
    refine hne (h r ((Polynomial.natDegree_lt_iff_degree_lt hne).2 h2) ?_)
    have := congrArg f hr.eq_mul_add
    rw [map_add (f := _), map_mul, h0, zero_mul, zero_add] at this
    exact this.symm.trans hx
  rw [hr.eq_mul_add, h3]
  simpa using Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self Q)

theorem isAdicComplete_span {A : Type} [CommRing A] (p : A) [IsAdicComplete (Ideal.span {p}) A] (Q b : A⟦X⟧)
    (d : ℕ) (hd : 0 < d) (hQ : Q = X ^ d + C p * b) :
    IsAdicComplete (Ideal.span {C p} ⊔ Ideal.span {Q}) A⟦X⟧ := by
  have hJ : (Ideal.span {p}).comap (constantCoeff (R := A)) = Ideal.span {C p} ⊔ Ideal.span {X} := by
    refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨y, hy⟩ : X ∣ x - C (constantCoeff x) := by rw [X_dvd_iff]; simp
      have h : x = C p * C c + X * y := by rw [← hy, ← map_mul, ← hc]; ring
      rw [h]
      exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simp
  have hc := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {p})
  rw [hJ] at hc
  refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le _ _ _ d 1 ?_ ?_ hc
  · have h1 : ∀ (I J : Ideal A⟦X⟧) (n : ℕ), (I ⊔ J) ^ n ≤ I ⊔ J ^ n := fun I J n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_succ]
        refine (Ideal.mul_mono_left ih).trans ?_
        rw [Ideal.sup_mul, Ideal.mul_sup (J ^ n)]
        exact sup_le (le_sup_of_le_left Ideal.mul_le_left)
          (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
    refine (h1 _ _ _).trans (sup_le le_sup_left ?_)
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
      show (X : A⟦X⟧) ^ d = -(C p * b) + Q by rw [hQ]; ring]
    exact Submodule.add_mem_sup (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_span_singleton_self _)
  · rw [pow_one]
    refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem, hQ, add_comm]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hd)

theorem existsUnique_series {A B κ : Type} [CommRing A] [CommRing B] {d : ℕ} (e : κ → (A →+* B)) (o : Fin d → B)
    (h : ∀ y : κ → B, ∃! c : Fin d → A, ∀ k, y k = ∑ i, o i * e k (c i)) (x : κ → B⟦X⟧) :
    ∃! c : Fin d → A⟦X⟧, ∀ k, x k = ∑ i, C (o i) * PowerSeries.map (e k) (c i) := by
  choose c hc hu using fun n => h fun k => coeff n (x k)
  refine ⟨fun i => PowerSeries.mk fun n => c n i, fun k => PowerSeries.ext fun n => ?_, fun c' hc' => ?_⟩
  · simpa [coeff_C_mul] using hc n k
  · funext i
    ext n
    rw [coeff_mk, ← hu n (fun i => coeff n (c' i)) fun k => by simp [hc' k, coeff_C_mul]]

end GlobalTheory.PrismS
end
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TransportCoef

open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (d0 d1 C1)

variable {O G : Type} [CommRing O] [Group G] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem rTensor_coefRep (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : M ⊗[O] X) :
    LinearMap.rTensor X e (coefRep W X g y) = coefRep W' X g (LinearMap.rTensor X e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [coefRep_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, coefRep_tmul, he]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem twist_intertwine (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (χ : G →* Oˣ) (g : G) (x : M) :
    e (twistRep W χ g x) = twistRep W' χ g (e x) := by
  rw [twistRep_apply, twistRep_apply, map_smul, he]

variable [TopologicalSpace G]

section General

variable {P P' : Type} [AddCommGroup P] [Module O P] [AddCommGroup P'] [Module O P']
  (π : Representation O G P) (π' : Representation O G P') (F : P →ₗ[O] P')
  (hF : ∀ g y, F (π g y) = π' g (F y))
include hF

theorem mem_Z1_comp {z : G → P} (hz : z ∈ Z1 π ⊤) : (fun g => F (z g)) ∈ Z1 π' ⊤ := by
  rw [Z1, Submodule.mem_inf] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨⟨h1.1.comp F, fun _ => Submodule.mem_top⟩, ?_⟩
  rw [LinearMap.mem_ker] at h2 ⊢
  funext x
  have := congrFun h2 x
  simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this ⊢
  rw [← hF, ← map_sub, ← map_add (f := _), this, map_zero]

theorem cob_comp {z : G → P} (S : Set G) (b : P) (hb : ∀ g ∈ S, z g = π g b - b) :
    ∀ g ∈ S, F (z g) = π' g (F b) - F b := by
  intro g hg
  rw [hb g hg, map_sub, hF]

theorem mem_B1_comp {z : G → P} (hz : z ∈ B1 π ⊤) : (fun g => F (z g)) ∈ B1 π' ⊤ := by
  rw [ReciprocityTheory.Def.B1, Submodule.mem_map] at hz ⊢
  obtain ⟨b, -, rfl⟩ := hz
  refine ⟨F b, Submodule.mem_top, ?_⟩
  funext g
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sub, hF]

end General

end GlobalTheory.TransportCoef

namespace GlobalTheory.TransportCoef
open Formalism.MainNotions.N (twistRep coefRep)

theorem transport {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x)) :
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  intro χ X _ _ z z' hzz
  have he' : ∀ g x, e.symm (W' g x) = W g (e.symm x) := fun g x => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let E := LinearEquiv.rTensor X e
  have hE : ∀ y, E y = LinearMap.rTensor X (e : M →ₗ[O] M') y := fun _ => rfl
  have hEs : ∀ y, E.symm y = LinearMap.rTensor X (e.symm : M' →ₗ[O] M) y := by
    intro y
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  have key : ∀ g y, (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (twCoef W χ X g y) = twCoef W' χ X g (E y) := fun g y =>
    rTensor_coefRep (twistRep W χ⁻¹) (twistRep W' χ⁻¹) (e : M →ₗ[O] M')
      (twist_intertwine W W' (e : M →ₗ[O] M') he χ⁻¹) X g y
  have keys : ∀ g y, (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (twCoef W' χ X g y) = twCoef W χ X g (E.symm y) :=
    fun g y => by
      show E.symm _ = _
      rw [hEs, hEs]
      exact rTensor_coefRep (twistRep W' χ⁻¹) (twistRep W χ⁻¹) (e.symm : M' →ₗ[O] M)
        (twist_intertwine W' W (e.symm : M' →ₗ[O] M) he' χ⁻¹) X g y
  have keyc : ∀ g y, E (coefRep W X g y) = coefRep W' X g (E y) := fun g y =>
    rTensor_coefRep W W' (e : M →ₗ[O] M') he X g y
  have hz'f : z' = fun g => (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (z g) := funext hzz
  have hzf : z = fun g => (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (z' g) := by
    funext g; show z g = E.symm (z' g); rw [hzz, LinearEquiv.symm_apply_apply]
  refine ⟨⟨fun hz => ?_, fun hz' => ?_⟩, ?_, ⟨fun hz => ?_, fun hz' => ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rw [hz'f]; exact mem_Z1_comp _ _ _ key hz
  · rw [hzf]; exact mem_Z1_comp _ _ _ keys hz'
  · intro hz hz' c hc
    refine ⟨E.prodCongr (LinearEquiv.refl O _), fun g x => ?_⟩
    obtain ⟨m, q⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearEquiv.prodCongr_apply, Ea_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.refl_apply, Ea_apply]
    simp only [Prod.mk.injEq, and_true]
    rw [map_add (f := _), map_smul, keyc, hzz]
  · rw [hz'f]; exact mem_B1_comp _ _ _ key hz
  · rw [hzf]; exact mem_B1_comp _ _ _ keys hz'
  · rintro ⟨b, hb⟩
    refine ⟨E b, fun g hg => ?_⟩
    rw [hzz]
    exact cob_comp _ _ _ key (I : Set G) b hb g hg
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, fun g hg => ?_⟩
    rw [hzf]
    exact cob_comp _ _ _ keys (I : Set G) b hb g hg

end GlobalTheory.TransportCoef
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem sen_near_of_abc : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m),
    ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 →
      ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  intro k _ l n m _ _ _ R D r Dt N₁ N₂ h₁ h₂ i y hy
  obtain ⟨hL₁, hAB₁, hC₁⟩ := h₁
  obtain ⟨hL₂, hAB₂, hC₂⟩ := h₂
  have e12 := CloseTw.main D Dt.h Dt.w N₁ N₂ hL₁ hL₂ hAB₁ hAB₂ i
  have e21 := CloseTw.main D Dt.h Dt.w N₂ N₁ hL₂ hL₁ hAB₂ hAB₁ i
  have hle : N₂ i ≤ sh (-(sg l Dt.h i : ℤ)) (N₁ i) := by
    have h' := sh_le_sh (-(sg l Dt.h i : ℤ)) e21
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  exact Compare.sen_compare R (D.γ i) (D.γ_semi i) (N₁ i) (N₂ i) (hL₁ i) (hL₂ i) (hC₁ i) (hC₂ i) _ e12 hle y hy

end GlobalTheory.Models
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.gammaNabla_mem_of_killing_polynomial : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  first | exact @GlobalTheory.GenKernelFit.nab_mem_of_ePoly | exact GlobalTheory.GenKernelFit.nab_mem_of_ePoly | (intros; apply GlobalTheory.GenKernelFit.nab_mem_of_ePoly <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exact_map_of_exact : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, Function.Exact (F.map A B f i) (F.map B C p i) := by
  first | exact @GlobalTheory.Models.DFun.map_exact_middle | exact GlobalTheory.Models.DFun.map_exact_middle | (intros; apply GlobalTheory.Models.DFun.map_exact_middle <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.obj_and_abc_of_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  first | exact @GlobalTheory.Models.model_obj_and_abc | exact GlobalTheory.Models.model_obj_and_abc | (intros; apply GlobalTheory.Models.model_obj_and_abc <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.model_sup_alt : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N N' : Lats k n A.m), M.Model A N → M.Model A N' → M.Model A (fun i => N i ⊔ N' i) := by
  first | exact @GlobalTheory.Models.SupModel.model_sup | exact GlobalTheory.Models.SupModel.model_sup | (intros; apply GlobalTheory.Models.SupModel.model_sup <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.phiGamma_lattice_families_shift_inclusion : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  first | exact @GlobalTheory.PhiGam.CloseTw.main | exact GlobalTheory.PhiGam.CloseTw.main | (intros; apply GlobalTheory.PhiGam.CloseTw.main <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_eq_sen_pre_add_sen_push : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  intro k G _ _ l n _ _ _ R F A B C f p N hB hf hp hfi hps hex i hN hc x
  have hA : F.Obj A := F.obj_sub A B f hf hfi hB
  have hC : F.Obj C := F.obj_quot B C p hp hps hB
  exact GlobalTheory.PhiGam.SenAdd.main R ((F.D B).γ i) ((F.D A).γ i) ((F.D C).γ i) (F.map A B f i) (F.map B C p i)
    ((F.D B).γ_semi i) (F.map_inj A B f hA hB hf hfi i) (F.map_surj B C p hB hC hp hps i)
    (GlobalTheory.Models.DFun.map_exact_middle F A B C f p hB hf hp hfi hps hex i) (F.map_γ A B f hA hB hf i) (F.map_γ B C p hB hC hp i)
    (N i) hN hc x

end GlobalTheory.Models
end

section

open GlobalTheory.LogU

theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0 → orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  first | exact @GlobalTheory.JR.Step.OrbULift.orbU_liftH | exact GlobalTheory.JR.Step.OrbULift.orbU_liftH | (intros; apply GlobalTheory.JR.Step.OrbULift.orbU_liftH <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.unramifiedBaseChange_latticeCount_eq : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ x : B.A, (overExt φ B ψ hψ hσ).N x = B.N x := by
  first | exact @GlobalTheory.UnitLemma.Unr.N_overExt | exact GlobalTheory.UnitLemma.Unr.N_overExt | (intros; apply GlobalTheory.UnitLemma.Unr.N_overExt <;> assumption)
end
