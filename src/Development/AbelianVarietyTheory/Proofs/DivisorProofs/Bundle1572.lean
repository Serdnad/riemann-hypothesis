module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pair_conj_mem_grp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  intro p _ G P B y s hs hc hβ
  refine ⟨?_, hc⟩
  change ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) * B * sh G ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * B
  have hmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← hmul, Units.inv_mul]; simp [sh]
  have hs0 : s ≠ 0 := hs.ne'
  have hβ' : (P.β : G.C) = s • ((y : G.C) * B * sh G y) := by rw [hβ, Algebra.smul_def]
  have hY : (y : G.C) * B * sh G y = s⁻¹ • (P.β : G.C) := by
    rw [hβ', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hsim : (P.γ : G.C) * P.β * sh G P.γ = (P.c : ℚ) • (P.β : G.C) := by
    rw [P.sim, Algebra.smul_def]
  rw [Units.val_mul, Units.val_mul, hmul, hmul, ← Algebra.smul_def]
  calc ((y⁻¹ : G.Cˣ) : G.C) * P.γ * y * B * (sh G y * (sh G P.γ * sh G ((y⁻¹ : G.Cˣ) : G.C)))
      = ((y⁻¹ : G.Cˣ) : G.C) * (P.γ * ((y : G.C) * B * sh G y) * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
        simp only [mul_assoc]
    _ = s⁻¹ • (((y⁻¹ : G.Cˣ) : G.C) * ((P.γ : G.C) * P.β * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hY]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ)) • (((y⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hsim, mul_smul]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ) * s) • ((((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
        rw [hβ', mul_smul (s⁻¹ * (P.c : ℚ)) s]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (P.c : ℚ) • (B : G.C) := by
        rw [Units.inv_mul, e, one_mul, mul_one, mul_comm (s⁻¹) _, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem grp_similitude_herm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : grp G β), ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ))ᴴ * herm G v β *
      (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β := by
  intro p _ G v β y
  obtain ⟨⟨u, s⟩, hy, _⟩ := y
  change (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β at hy
  have hV : ((toV G v β ⟨(u, s), hy, ‹_›⟩ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (u : G.C) := rfl
  rw [hV]
  change (G.psi v (u : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) * G.psi v (u : G.C) =
    ((s : ℚ) : ℂ) • (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C))
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hu : sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u =
      algebraMap ℚ G.C (s : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (u * β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (u : G.C) * β * (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u)
        = ((u : G.C) * β * sh G (u : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) * u := by
          simp only [mul_assoc]
      _ = (s : ℚ) • ((β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
          rw [hy, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (s : ℚ) • ((u : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (u : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (u : G.C)
      = G.gram v * (G.psi v (sh G (u : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (u : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (u : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * u) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((s : ℚ) : ℚ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKCx
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem commute_units_conj {A : Type*} [Monoid A] (U : Aˣ) {a e : A} (h : Commute a e) :
    Commute ((U : A) * a * ↑U⁻¹) ((U : A) * e * ↑U⁻¹) := by
  unfold Commute SemiconjBy at *
  calc (U : A) * a * ↑U⁻¹ * ((U : A) * e * ↑U⁻¹) = U * (a * e) * ↑U⁻¹ := by
        simp only [mul_assoc, Units.inv_mul_cancel_left]
    _ = U * (e * a) * ↑U⁻¹ := by rw [h]
    _ = _ := by simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem comm_of_conj {A : Type*} [Monoid A] (U : Aˣ) (e : A)
    (h : ∀ a b : A, Commute a ((U : A) * e * ↑U⁻¹) → Commute b ((U : A) * e * ↑U⁻¹) → Commute a b)
    (a b : A) (ha : Commute a e) (hb : Commute b e) : Commute a b := by
  have h1 := h _ _ (commute_units_conj U ha) (commute_units_conj U hb)
  have h2 := commute_units_conj U⁻¹ h1
  have e1 : ∀ z : A, ((U⁻¹ : Aˣ) : A) * ((U : A) * z * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = z := by
    intro z; simp [mul_assoc]
  rwa [e1, e1] at h2

variable {p : ℕ} [Fact p.Prime]

theorem ubc_val_eq (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t)
    (y : grp G β) (h : G.GAf) (w : AwayP p) :
    ∃ U : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
    ((ubcMap (AfP.eval w) (h⁻¹ * toAfF G β x t hx y * h)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      (U : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
        ((U⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
  set φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C :=
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) with hφ
  have hm : ((ubcMap (AfP.eval w) (toAfF G β x t hx y)).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      φ x * ((1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * φ ↑x⁻¹ := by
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ↑x⁻¹) = _
    rw [map_mul, map_mul]
    congr 2
  refine ⟨((ubcMap (AfP.eval w) h).1.1)⁻¹ * Units.map φ.toMonoidHom x, ?_⟩
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, Units.val_mul, _root_.mul_inv_rev, inv_inv]
  rw [hm]
  simp only [Units.coe_map, MonoidHom.coe_coe, mul_assoc]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem continuous_gAf_fst (G : HTGroup p) :
    @Continuous G.GAf (AfP p ⊗[ℚ] G.C) _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C))
      (fun g => (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_gAf_snd_inv (G : HTGroup p) :
    Continuous (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_subtype_val))

theorem exists_compact_of_isTest (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (h₁ : G.GAf) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f (h₁⁻¹ * g * h₁) ≠ 0 → g ∈ Q := by
  obtain ⟨S, hS⟩ := hf.2.2.2
  have hK : IsCompact (L.K : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun q : G.GAf × G.GAf => h₁ * (q.1 * s * q.2) * h₁⁻¹) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, he⟩ := hS _ hg
  refine Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, ?_⟩
  show h₁ * (k₁ * s * k₂) * h₁⁻¹ = g
  rw [← he]; group

theorem exists_compact_toAfF : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (h₁ : G.GAf), ∃ (Ω : Set (AfP p ⊗[ℚ] G.C)) (Ω' : Set (AfP p)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) Ω ∧ IsCompact Ω' ∧ ∀ y : grp G β,
    f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ Ω ∧
    algebraMap ℚ (AfP p) ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹) ∈ Ω' := by
  intro p _ G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  obtain ⟨Q, hQ, hmem⟩ := exists_compact_of_isTest G L f hf h₁
  refine ⟨(fun g : G.GAf => ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * x) '' Q,
    (fun g : G.GAf => ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p)) '' Q,
    hQ.image ((continuous_const.mul (continuous_gAf_fst G)).mul continuous_const),
    hQ.image (continuous_gAf_snd_inv G), fun y hy => ⟨⟨_, hmem _ hy, ?_⟩, ⟨_, hmem _ hy, ?_⟩⟩⟩
  · show ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
      ((x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
        AfP p ⊗[ℚ] G.C) * x = _
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · show (((Units.map (algebraMap ℚ (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).2))⁻¹ : (AfP p)ˣ) : AfP p) = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl

end GlobalTheory.LKCx
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

noncomputable def centEquiv (G : HTGroup p) (P : Pair G) (hpos : ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ))
    (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    Subgroup.centralizer ({r} : Set (grp G P.β)) ≃* P.cent where
  toFun y := ⟨y.1.1, by
    have h := congrArg (fun a : grp G P.β => (a : G.Cˣ × ℚˣ).1)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2)
    simp only [Subgroup.coe_mul, hr, Prod.fst_mul] at h
    exact h, y.1.2.1⟩
  invFun y := ⟨⟨y.1, y.2.2, hpos y.1 y.2⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hr]
    exact Prod.ext y.2.1 (mul_comm _ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fix_iff_mark (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (P : Pair G) (r : grp G P.β) (hr : (r : G.Cˣ × ℚˣ) = (P.γ, P.c)) :
    (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) ↔ ∃ μ, P.Mark μ := by
  have hV : (toV G v P.β r : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v (P.γ : G.C) := by
    show G.psi v (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = _
    rw [hr]
  constructor
  · rintro ⟨z, hz, c, hc⟩
    rw [hV] at hc
    exact ⟨c, v, hv, z, hc, hz⟩
  · rintro ⟨μ, w, hw, z, hz, hpos⟩
    have h1 : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := hG.le
    have hvv : w = v := congrArg Subtype.val (Fintype.card_le_one_iff.1 h1 ⟨w, hw⟩ ⟨v, hv⟩)
    subst hvv
    exact ⟨z, hpos, μ, by rw [hV]; exact hz⟩

end GlobalTheory.LKCx.Regroup
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.Div

theorem conj_of_twist : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y₁ y₂ : grp G β) (y₀ c₁ c₂ w : G.Cˣ) (r : ℚ),
    (((y₁ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₁ * y₀ * ((c₁⁻¹ : G.Cˣ) : G.C) →
    (((y₂ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₂ * y₀ * ((c₂⁻¹ : G.Cˣ) : G.C) →
    (y₁ : G.Cˣ × ℚˣ).2 = (y₂ : G.Cˣ × ℚˣ).2 → Commute (w : G.C) y₀ → 0 < r →
    (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) →
    ∃ γ : grp G β, y₂ = γ * y₁ * γ⁻¹ := by
  intro p _ G β y₁ y₂ y₀ c₁ c₂ w r h1 h2 hs hw hr H
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shc : sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C) = 1 := by
    rw [← shm, Units.mul_inv]; simp [sh]
  have hR : algebraMap ℚ G.C r⁻¹ * algebraMap ℚ G.C r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  set ru : ℚˣ := Units.mk0 r hr.ne' with hru

  have HX : (w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r⁻¹ *
      (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    rw [H, ← mul_assoc (algebraMap ℚ G.C r⁻¹), hR, one_mul]
  have mem : ((c₂ * w * c₁⁻¹, ru⁻¹) : G.Cˣ × ℚˣ) ∈ grp G β := by
    refine ⟨?_, ?_⟩
    · change ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((ru⁻¹ : ℚˣ) : ℚ) * β
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]
      simp only [Units.val_mul, shm]
      calc (c₂ : G.C) * w * ((c₁⁻¹ : G.Cˣ) : G.C) * β * (sh G ((c₁⁻¹ : G.Cˣ) : G.C) * (sh G (w : G.C) * sh G (c₂ : G.C)))
          = c₂ * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
            ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) * β * sh G (c₂ : G.C) := by
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = algebraMap ℚ G.C r⁻¹ * ((c₂ : G.C) * ((c₂⁻¹ : G.Cˣ) : G.C) * β *
              (sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C))) := by
            rw [HX, Algebra.left_comm]
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = _ := by rw [shc, Units.mul_inv, one_mul, mul_one]
    · change 0 < ((ru⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]; exact inv_pos.2 hr
  refine ⟨⟨_, mem⟩, ?_⟩
  have e1 : (y₁ : G.Cˣ × ℚˣ).1 = c₁ * y₀ * c₁⁻¹ := Units.ext (by rw [h1]; simp)
  have e2 : (y₂ : G.Cˣ × ℚˣ).1 = c₂ * y₀ * c₂⁻¹ := Units.ext (by rw [h2]; simp)
  have hwu : w * y₀ = y₀ * w := Units.ext (by simpa using hw.eq)
  have hwu' : ∀ x : G.Cˣ, w * (y₀ * x) = y₀ * (w * x) := fun x => by rw [← mul_assoc, hwu, mul_assoc]
  apply Subtype.ext
  apply Prod.ext
  · show (y₂ : G.Cˣ × ℚˣ).1 = (c₂ * w * c₁⁻¹) * (y₁ : G.Cˣ × ℚˣ).1 * (c₂ * w * c₁⁻¹)⁻¹
    rw [e1, e2]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, hwu', mul_inv_cancel_left]
  · show (y₂ : G.Cˣ × ℚˣ).2 = ru⁻¹ * (y₁ : G.Cˣ × ℚˣ).2 * ru⁻¹⁻¹
    rw [hs, mul_comm ru⁻¹, mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.Div
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem unit_conj_form_props {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β Y c : G.Cˣ) (s : ℚ) (hβ : sh G β = β)
    (h0 : (Y : G.C) * β * sh G Y = algebraMap ℚ G.C s * β)
    (h1 : ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) =
      algebraMap ℚ G.C s * β) :
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧
    Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (Y : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β⁻¹ : G.Cˣ) : G.C) = ((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
  have shm : ∀ x z : G.C, sh G (x * z) = sh G z * sh G x := fun x z => by simp [sh]
  have shs : ∀ x : G.C, sh G (sh G x) = x := G.star_star
  have sh1 : sh G 1 = 1 := sh_one_eq G
  set u : G.C := ((c⁻¹ : G.Cˣ) : G.C) with hu
  set bi : G.C := ((β⁻¹ : G.Cˣ) : G.C) with hbi_def
  set S : G.C := algebraMap ℚ G.C s with hS
  have hA : ∀ r : G.C, u * ((c : G.C) * r) = r := fun r => by rw [← mul_assoc, hu, Units.inv_mul, one_mul]
  have hB : sh G (c : G.C) * sh G u = 1 := by rw [← shm, hu, Units.inv_mul, sh1]
  have hB' : ∀ r : G.C, sh G (c : G.C) * (sh G u * r) = r := fun r => by rw [← mul_assoc, hB, one_mul]
  have hC : ∀ r : G.C, (β : G.C) * (bi * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.mul_inv, one_mul]
  have hC' : ∀ r : G.C, bi * ((β : G.C) * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.inv_mul, one_mul]
  have hD : (β : G.C) * bi = 1 := by rw [hbi_def, Units.mul_inv]
  set shYi : G.C := sh G ((Y⁻¹ : G.Cˣ) : G.C) with hshYi
  have hE : ∀ r : G.C, sh G (Y : G.C) * (shYi * r) = r := fun r => by
    rw [← mul_assoc, hshYi, ← shm, Units.inv_mul, sh1, one_mul]
  have hE1 : sh G (Y : G.C) * shYi = 1 := by rw [hshYi, ← shm, Units.inv_mul, sh1]
  refine ⟨?_, ?_, ?_⟩
  · have hshu : IsUnit (sh G u) := ⟨⟨sh G u, sh G (c : G.C), by rw [← shm, hu, Units.mul_inv, sh1], hB⟩, rfl⟩
    exact (((Units.isUnit _).mul (Units.isUnit β)).mul hshu).mul (Units.isUnit _)
  · have h2 : (Y : G.C) * (u * β * sh G u) * sh G Y = S * (u * β * sh G u) := by
      calc (Y : G.C) * (u * β * sh G u) * sh G Y
          = u * (((c : G.C) * Y * u) * β * sh G ((c : G.C) * Y * u)) * sh G u := by
            simp only [shm, mul_assoc, hA, hB, hB', mul_one]
        _ = S * (u * β * sh G u) := by
            rw [h1, hS, ← mul_assoc, ← Algebra.commutes s u]; simp only [mul_assoc]
    have e1 : (Y : G.C) * (u * β * sh G u * bi) = S * ((u * β * sh G u) * (shYi * bi)) := by
      calc (Y : G.C) * (u * β * sh G u * bi) = ((Y : G.C) * (u * β * sh G u) * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE]
        _ = _ := by rw [h2, mul_assoc]
    have eY : (Y : G.C) = S * ((β : G.C) * (shYi * bi)) := by
      calc (Y : G.C) = ((Y : G.C) * β * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE, hD, mul_one]
        _ = _ := by rw [h0, mul_assoc]
    have e2 : (u * β * sh G u * bi) * (Y : G.C) = S * ((u * β * sh G u) * (shYi * bi)) := by
      rw [eY]
      calc u * β * sh G u * bi * (S * ((β : G.C) * (shYi * bi)))
          = (u * β * sh G u) * (bi * S * ((β : G.C) * (shYi * bi))) := by simp only [mul_assoc]
        _ = (u * β * sh G u) * (S * (bi * ((β : G.C) * (shYi * bi)))) := by
            rw [hS, ← Algebra.commutes s bi]; simp only [mul_assoc]
        _ = _ := by rw [hC', ← mul_assoc, ← mul_assoc, ← Algebra.commutes s, hS]; simp only [mul_assoc]
    exact e2.trans e1.symm
  · have hbi : sh G bi = bi := by
      have h3 : sh G (β : G.C) * sh G bi = 1 := by rw [← shm, hbi_def, Units.inv_mul, sh1]
      rw [hβ] at h3
      calc sh G bi = (bi * β) * sh G bi := by rw [hbi_def, Units.inv_mul, one_mul]
        _ = bi := by rw [mul_assoc, h3, mul_one]
    simp only [shm, shs, hβ, hbi, mul_assoc, hC]

theorem grp_conj_unit_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 →
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) = (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ y y₀ c hy hs
  have h0 : (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) * β := y₀.2.1
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y : G.Cˣ × ℚˣ).2 : ℚ) * β := y.2.1
  rw [hy, hs] at h1
  exact unit_conj_form_props G β _ c _ hβ h0 h1

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixLine_conj_iff {n : Type} [Fintype n] [DecidableEq n] (A B : GL n ℂ) (z : n → ℂ) :
    (∃ c : ℂ, (A : Matrix n n ℂ) *ᵥ z = c • z) ↔
      ∃ c : ℂ, ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
        c • ((B : Matrix n n ℂ) *ᵥ z) := by
  have key : ((B * A * B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ ((B : Matrix n n ℂ) *ᵥ z) =
      (B : Matrix n n ℂ) *ᵥ ((A : Matrix n n ℂ) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [key, hc, Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [key, ← Matrix.mulVec_smul] at hc
    have h := congrArg (fun w => ((B⁻¹ : GL n ℂ) : Matrix n n ℂ) *ᵥ w) hc
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h
    rwa [inv_mul_cancel_left] at h

theorem fixL_conj_iff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y g : grp G β) (z : Fin G.n → ℂ),
    FixL G v β y z ↔ FixL G v β (g * y * g⁻¹) ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  intro p _ G v β y g z
  unfold FixL
  rw [map_mul, map_mul, map_inv]
  exact fixLine_conj_iff _ _ z

end GlobalTheory.LKCx
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    (∃ N' : Submodule R (primDR A), IsCompl (PrimitiveSubmodule A) N') →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ l : Module.Dual R (PrimitiveSubmodule A), ∃ x : G.Lie, ∀ c, x (ψ c) = l c :=
  @GlobalTheory.PtExt.exists_lie_comp_psi_eq
end
