module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Ring

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

private theorem sim_triv (σ : S →+* Sᵐᵒᵖ) (b b' : S) (x x' Y : Sˣ) (t t' T : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b' * (σ x').unop = algebraMap A S t')
    (hb : b' = algebraMap A S T * ((Y : S) * b * (σ Y).unop)) :
    ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop =
      algebraMap A S ((t' * T⁻¹ * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h0 : b = (t : A) • (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ x).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hx, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = ((t⁻¹ : Aˣ) : A) • b := by
    conv_rhs => rw [h0]
    rw [smul_smul, Units.inv_mul, one_smul]
  have h3 : (Y : S) * b * (σ Y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  calc ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop
      = x' * (Y * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ Y).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • (x' * ((Y : S) * b * (σ Y).unop) * (σ x').unop) := by
        rw [h2]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • ((T⁻¹ : Aˣ) : A) • ((x' : S) * b' * (σ x').unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := by
        rw [hx', Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul]
        ring

private theorem sim_conj (σ : S →+* Sᵐᵒᵖ) (b b' : S) (z y : Sˣ) (T : Aˣ) (r : A)
    (hb : b' = algebraMap A S T * ((y : S) * b * (σ y).unop))
    (hz : (z : S) * b' * (σ z).unop = algebraMap A S r * b') :
    ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop = algebraMap A S r * b := by
  have h1 : (σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h3 : (y : S) * b * (σ y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  rw [← Algebra.smul_def] at hz ⊢
  calc ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop
      = ((y⁻¹ : Sˣ) : S) * ((z : S) * ((y : S) * b * (σ y).unop) * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((T⁻¹ : Aˣ) : A) • (((y⁻¹ : Sˣ) : S) * ((z : S) * b' * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = r • (((y⁻¹ : Sˣ) : S) * (((T⁻¹ : Aˣ) : A) • b') * (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [hz]; simp only [mul_smul_comm, smul_mul_assoc]; rw [smul_comm]
    _ = r • ((((y⁻¹ : Sˣ) : S) * y) * b * ((σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop)) := by
        rw [← h3]; simp only [mul_assoc]
    _ = r • b := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Ring

private theorem mem_forms_move {A H V : Type} [Group A] [Group H] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (Γ Γ' : Subgroup A) (ι : Γ →* H) (ι' : Γ' →* H) (K : Subgroup H) (y : A) (d : H)
    (hc : ∀ γ' : Γ', ∃ γ : Γ, (γ' : A) = y * (γ : A) * y⁻¹ ∧ ι' γ' = d * ι γ * d⁻¹)
    {Φ : H → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι K (ξ.comp Γ.subtype)) :
    (fun g => ξ y (Φ (d⁻¹ * g))) ∈ HeckeTraceForms.forms ι' K (ξ.comp Γ'.subtype) := by
  refine ⟨fun γ' g => ?_, fun k hk g => ?_⟩
  · obtain ⟨γ, e1, e2⟩ := hc γ'
    have e3 : d⁻¹ * (ι' γ' * g) = ι γ * (d⁻¹ * g) := by rw [e2]; group
    have e4 : Φ (ι γ * (d⁻¹ * g)) = ξ (γ : A) (Φ (d⁻¹ * g)) := hΦ.1 γ (d⁻¹ * g)
    show ξ y (Φ (d⁻¹ * (ι' γ' * g))) = ξ (γ' : A) (ξ y (Φ (d⁻¹ * g)))
    rw [e3, e4, e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · show ξ y (Φ (d⁻¹ * (g * k))) = ξ y (Φ (d⁻¹ * g))
    rw [← mul_assoc]
    exact congrArg _ (hΦ.2 k hk _)

variable {p : ℕ} [Fact p.Prime]

private theorem op_move {G : HTGroup p} {A V : Type} [Group A] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (K : Subgroup G.GAf) (f : G.GAf → ℂ) (Φ : G.GAf × Gr G 1 → V) (y : A)
    (d : G.GAf × Gr G 1) :
    op K f (fun g => ξ y (Φ (d⁻¹ * g))) = fun g => ξ y (op K f Φ (d⁻¹ * g)) := by
  funext g
  let L : V ≃+ V :=
    { toFun := ξ y
      invFun := ξ y⁻¹
      left_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      right_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      map_add' := map_add _ }
  show ∑ᶠ h : G.GAf ⧸ K, f h.out • ξ y (Φ (d⁻¹ * (g * (h.out, 1)))) =
    L (∑ᶠ h : G.GAf ⧸ K, f h.out • Φ (d⁻¹ * g * (h.out, 1)))
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun h => ?_
  show _ = ξ y (_ • _)
  rw [map_smul, mul_assoc]

private theorem conj_emb (G : HTGroup p) (B B' : DForm G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (B'.β : G.C) = algebraMap ℚ G.C s * (y * B.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
    (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ) (hx' : Triv G (AfP p) B'.β x' t') :
    ∃ d : G.GAf × Gr G 1, ∀ γ' : grp G B'.β, ∃ γ : grp G B.β,
      (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (γ : G.Cˣ × ℚˣ) * ((y, 1) : G.Cˣ × ℚˣ)⁻¹ ∧
      B'.embAt x' t' hx' γ' = d * B.embAt x t hx γ * d⁻¹ := by
  let Y : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y
  let T : (AfP p)ˣ := Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs.ne')
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) := by
    show _ = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s)
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  have hb : inC G (AfP p) B'.β = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) *
      ((Y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) B.β * (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop) := by
    rw [hβ, map_mul, map_mul, map_mul, e1, e2]
    rfl
  have hc := sim_triv (starT G.star (AfP p)) _ _ x x' Y t t' T hx hx' hb
  let c : G.GAf := ⟨(x' * Y * x⁻¹, t' * T⁻¹ * t⁻¹), hc⟩
  refine ⟨(c, inclG G 1 (locC G (y, 1))), fun γ' => ?_⟩
  have hz : ((γ'.1.1 : G.Cˣ) : G.C) * B'.β * (G.star ((γ'.1.1 : G.Cˣ) : G.C)).unop =
      algebraMap ℚ G.C (γ'.1.2 : ℚ) * B'.β := γ'.2.1
  have hmem : ((y⁻¹ * γ'.1.1 * y, γ'.1.2) : G.Cˣ × ℚˣ) ∈ grp G B.β :=
    ⟨sim_conj G.star (B.β : G.C) (B'.β : G.C) γ'.1.1 y (Units.mk0 s hs.ne') (γ'.1.2 : ℚ) hβ hz, γ'.2.2⟩
  have hconj : (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (y⁻¹ * γ'.1.1 * y, γ'.1.2) *
      ((y, 1) : G.Cˣ × ℚˣ)⁻¹ := by
    refine Prod.ext ?_ ?_
    · simp [mul_assoc]
    · simp
  refine ⟨⟨_, hmem⟩, hconj, ?_⟩
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
  · show x' * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * x'⁻¹ =
      (x' * Y * x⁻¹) * (x * Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) * x⁻¹) *
        (x' * Y * x⁻¹)⁻¹
    have e3 : Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) =
        Y⁻¹ * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * Y := by
      rw [map_mul, map_mul, map_inv]
    rw [e3]
    group
  · have e3 : ∀ a b : (AfP p)ˣ, b = a * b * a⁻¹ := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right]
    exact e3 (t' * T⁻¹ * t⁻¹) (Units.map (algebraMap ℚ (AfP p)).toMonoidHom γ'.1.2)
  · have e3 := congrArg ((inclG G 1).comp (locC G)) hconj
    rw [map_mul, map_mul, map_inv] at e3
    exact e3

theorem clsMove : ClsMove := by
  intro p _ G V _ _ ξ K J ψ θ e ⟨B, x, t, hx, Φ, hΦ, h0, he, hψ⟩
  have hrel : DForm.Rel B (Quot.out (Quot.mk _ B : DFCls G)) :=
    (GlobalTheory.LKDef.Regroup.dform_rel_equivalence.eqvGen_iff).1
      (Quot.eqvGen_exact (Quot.out_eq (Quot.mk DForm.Rel B)).symm)
  obtain ⟨y, s, hs, hβ⟩ := hrel
  obtain ⟨d, hd⟩ := conj_emb G B _ y s hs hβ x t hx _ _
    (Quot.out (Quot.mk _ B : DFCls G)).trivAf.choose_spec.choose_spec
  refine ⟨Quot.mk _ B, fun g => ξ (y, 1) (Φ (d⁻¹ * g)),
    mem_forms_move ξ _ _ _ _ _ _ d hd hΦ, fun h => h0 ?_, ?_, fun j => ?_⟩
  · funext g
    have := congrFun h (d * g)
    simp only [inv_mul_cancel_left, Pi.zero_apply] at this
    have h2 := congrArg (ξ ((y, 1) : G.Cˣ × ℚˣ)⁻¹) this
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h2
    exact h2
  · rw [op_move, he]
  · rw [op_move, hψ j]
    funext g
    simp

end UpperTheory.Gal.Spc
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCx GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo (Integ IsFnL)
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

instance algAt (S : Setup A n p) (w : Plc E) : Algebra S.G.F (w.adicCompletion E) := inferInstanceAs (Algebra E (w.adicCompletion E))

def Spl (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ) : Type := {w : Plc E // IsSplitAt w ∧ (p : 𝓞 E) ∉ w.asIdeal}

abbrev fac {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Spl E p) : Loc S.G.GAf (GL (Fin n) (w.1.adicCompletion E)) :=
  T.at hc w.1 w.2.1 w.2.2

structure Half (q : ℕ) (W : Finset (Spl E p)) : Prop where
  above : ∀ w ∈ W, (q : 𝓞 E) ∈ w.1.asIdeal
  all : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → ∃ w ∈ W, w.1 = u ∨ cj w.1 = u
  apart : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → GlobalTheory.Cong.Apart w.1 w'.1

def AdmCusp : Prop :=
  ∀ (X : Type) [Group X] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ) (Ty : TyLev X (GL (Fin n) k)),
    IsOpen (Ty.J : Set (GL (Fin n) k)) → IsCompact (Ty.J : Set (GL (Fin n) k)) → IsOpen (Ty.ψ.ker : Set Ty.J) →
    (∀ (σ : SmIrr (GL (Fin n) k)) (v : σ.V), v ≠ 0 → (∀ g : Ty.J, σ.ρ g v = ((Ty.ψ g : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) →
    ∀ f, Ty.admitted f → ∀ h : X, Ty.L.pr h = 1 → NoConst fun g => f (Ty.L.loc g * h)

end UpperTheory.Gal.Spc
end
end

section

set_option autoImplicit false

open Formalism.UG (Hecke conv IsCommensurated)
open UpperTheory.Gal.LocalSmoothExtension (wordFn polyFn)

namespace UpperTheory.Gal.Spc

section Abstract

variable {H J : Type} [Group H] {K : Subgroup H}

private theorem word_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (w : List J) : wordFn K ψ w f ∈ Hecke ℂ K := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ (hψ j) _ ih

private theorem poly_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : polyFn K ψ s f ∈ Hecke ℂ K := by
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (word_mem hK hψ hf w)

private theorem pow_mem (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (n : ℕ) :
    powFn K u e n ∈ Hecke ℂ K := by
  induction n with
  | zero => exact he
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ hu _ ih

private theorem fix_step (hK : IsCommensurated K) {e t x : H → ℂ} (he : e ∈ Hecke ℂ K) (ht : t ∈ Hecke ℂ K)
    (hx : x ∈ Hecke ℂ K) (hte : conv K e (conv K t e) = conv K t e) (hex : conv K e x = x) :
    conv K e (conv K t x) = conv K t x := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K e (conv K t x) = conv K e (conv K t (conv K e x)) := by rw [hex]
    _ = conv K e (conv K (conv K t e) x) := by rw [A t ht e he x hx]
    _ = conv K (conv K e (conv K t e)) x := by rw [A e he (conv K t e) (M t ht e he) x hx]
    _ = conv K (conv K t e) x := by rw [hte]
    _ = conv K t (conv K e x) := by rw [A t ht e he x hx]
    _ = conv K t x := by rw [hex]

private theorem pow_fix (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K)
    (hidem : conv K e e = e) (heu : conv K e (conv K u e) = conv K u e) (n : ℕ) :
    conv K e (powFn K u e n) = powFn K u e n := by
  induction n with
  | zero => exact hidem
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact fix_step hK he hu (pow_mem hK hu he n) heu ih

private theorem word_fix (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {e f : H → ℂ}
    (he : e ∈ Hecke ℂ K) (hf : f ∈ Hecke ℂ K) (heT : ∀ j, conv K e (conv K (ψ j) e) = conv K (ψ j) e)
    (hef : conv K e f = f) (w : List J) : conv K e (wordFn K ψ w f) = wordFn K ψ w f := by
  induction w with
  | nil => exact hef
  | cons j w ih => exact fix_step hK he (hψ j) (word_mem hK hψ hf w) (heT j) ih

private theorem comm_fix (hK : IsCommensurated K) {e a b x : H → ℂ} (he : e ∈ Hecke ℂ K) (ha : a ∈ Hecke ℂ K)
    (hb : b ∈ Hecke ℂ K) (hx : x ∈ Hecke ℂ K) (hab : conv K a (conv K b e) = conv K b (conv K a e))
    (hex : conv K e x = x) : conv K a (conv K b x) = conv K b (conv K a x) := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K a (conv K b x) = conv K a (conv K b (conv K e x)) := by rw [hex]
    _ = conv K a (conv K (conv K b e) x) := by rw [A b hb e he x hx]
    _ = conv K (conv K a (conv K b e)) x := by rw [A a ha (conv K b e) (M b hb e he) x hx]
    _ = conv K (conv K b (conv K a e)) x := by rw [hab]
    _ = conv K b (conv K (conv K a e) x) := by rw [A b hb (conv K a e) (M a ha e he) x hx]
    _ = conv K b (conv K a (conv K e x)) := by rw [A a ha e he x hx]
    _ = conv K b (conv K a x) := by rw [hex]

private theorem conv_supp {a f : H → ℂ} {g : H} (h : conv K a f g ≠ 0) : ∃ x : H, a x ≠ 0 ∧ f (x⁻¹ * g) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold Formalism.UG.conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_cases ha : a (Quotient.out q) = 0
  · rw [ha, zero_mul]
  · rw [hc _ ha, mul_zero]

private theorem word_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (w : List J) : ∀ g, wordFn K ψ w f g ≠ 0 → g ∈ R := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    intro g hg
    obtain ⟨x, hx1, hx2⟩ := conv_supp (K := K) (a := ψ j) (f := wordFn K ψ w f) hg
    have hx := hR j x hx1 _ (ih _ hx2)
    simpa using hx

private theorem poly_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (s : List J →₀ ℂ) (g : H) (hg : polyFn K ψ s f g ≠ 0) : g ∈ R := by
  by_contra hgR
  apply hg
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  rw [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [Pi.smul_apply, smul_eq_mul]
  have hw : wordFn K ψ w f g = 0 := by
    by_contra hne
    exact hgR (word_supp (K := K) hR hf w g hne)
  rw [hw, mul_zero]

end Abstract

theorem words : Words := by
  intro p _ G Lv J ψ e u u' hψ he hu hrel n
  have hK : IsCommensurated (Lv.K : Subgroup G.GAf) :=
    PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ Lv.K.isOpen Lv.compact
  have hP := pow_mem hK hu he n
  have hfix := pow_fix hK hu he hrel.idem hrel.eu n
  refine ⟨hP, fun s => poly_mem hK hψ hP s, fun j j' w => ?_, fun R hR hf s g hg => poly_supp hR hf s g hg⟩
  exact comm_fix hK he (hψ j) (hψ j') (word_mem hK hψ hP w) (hrel.TT j j') (word_fix hK hψ he hP hrel.eT hfix w)

end UpperTheory.Gal.Spc
end
