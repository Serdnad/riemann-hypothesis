module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle013
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
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
import Mathlib.GroupTheory.Nilpotent
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem exists_top_embedding_eq_on_countable (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ)
    (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let A : Set M := {y | (y : ℂ) ∈ S}
  have hA : A.Countable := hS.preimage Subtype.val_injective
  let k : Subfield M := Subfield.closure A
  haveI : Countable k := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max A).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hA.to_subtype
  obtain ⟨τ, hτ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := k)
    ((M.val : M →+* ℂ).comp k.subtype) ((ρ : M →+* ℂ).comp k.subtype)
  refine ⟨(τ.toRingHom.toRatAlgHom).comp (⊤ : IntermediateField ℚ ℂ).val, fun x hx hxM => ?_⟩
  have h := hτ ⟨⟨x, hxM⟩, Subfield.subset_closure hx⟩
  have h1 : liftM ⊤ x = ⟨x, IntermediateField.mem_top⟩ := dif_pos IntermediateField.mem_top
  have h2 : liftM M x = ⟨x, hxM⟩ := dif_pos hxM
  unfold cj
  rw [h1, h2]
  exact h

end GlobalTheory.GalTheta
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.MovedTheta

open Matrix GlobalTheory.NormSum.AdLattice

variable {D : D7} {N N' : ℕ}

def mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) (AE D) :=
  ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
    (g : Matrix (Fin N) (Fin N) (AE D))

theorem mv_zero (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) : mv g g' 0 = 0 := by
  unfold mv
  rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

theorem mv_add (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z + w) = mv g g' z + mv g g' w := by
  unfold mv
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem mv_smul (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (e : D.host.E)
    (z : Matrix (Fin N') (Fin N) D.host.E) : mv g g' (e • z) = inc D e • mv g g' z := by
  unfold mv
  have : (e • z).map (inc D) = inc D e • z.map (inc D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem inc_int (o : 𝓞 D.host.E) : inc D (o : D.host.E) ∈ OhE D :=
  Formalism.UG.P.adelstab_incl_int (F := ℚ) o

theorem mulVec_mem_of_span {R m n : Type} [CommRing R] [Fintype n] {S : Subring R} (M : Matrix m n R) (i : m)
    {T : Set (n → R)} (hT : ∀ u ∈ T, (M *ᵥ u) i ∈ S) {u : n → R} (hu : u ∈ Submodule.span S T) :
    (M *ᵥ u) i ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hT u hu
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    have e : s • u = (s : R) • u := rfl
    rw [e, mulVec_smul]
    exact mul_mem s.2 hu

theorem mv_int_of_maps {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  let Λ := Formalism.UG.stdLat (n := Fin N) (A := D.host.E) (𝓞 D.host.E)
  have hstd (v : Fin N → AE D) :
      v ∈ Formalism.UG.latS (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (OhE D) Λ ↔
        ∀ i, v i ∈ OhE D := by
    dsimp [Λ, OhE]
    rw [Formalism.UG.P.easyc_latS_std]
    exact Formalism.UG.P.adelstab_mem_stdLat (F := ℚ) (E := D.host.E) v
  have hL : L = Formalism.UG.CS.globLat g Λ := by
    ext x
    exact (h x).trans (hstd _).symm
  have h1 := (Formalism.UG.P.span_recovery_of_integral_adelic_approx
    Formalism.UG.P.csGlob_intAdApprox ℚ D.host.E (Fin N) Λ
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).1
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).2
    g ((g : Matrix (Fin N) (Fin N) (AE D)) *ᵥ Pi.single j 1)).2 (hstd _ |>.2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _))
  have h3 := mulVec_mem_of_span
    (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D)) i (by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (h' _).1 (hA x (hL ▸ hx)) i
      have e : (fun j => inc D ((A *ᵥ x) j)) = A.map (inc D) *ᵥ (fun j => inc D (x j)) := by
        ext k; rw [RingHom.map_mulVec]; rfl
      rw [e, mulVec_mulVec] at h2
      exact h2) h1
  rw [mulVec_mulVec, mulVec_single_one] at h3
  exact h3

theorem mv_int_of_hom {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact mv_int_of_maps h h' hA i j
  | zero => rw [mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, mv_smul]
    exact mul_mem (inc_int o) hu

theorem mul_mem_IhE {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | neg u _ hu => rw [mul_neg]; exact neg_mem hu

theorem mv_mem_IhE {cc : Ideal (𝓞 D.host.K)} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') (i : Fin N') (j : Fin N) :
    mv g g' (((c : D.host.K) : D.host.E) • B) i j ∈ IhE D cc := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    rw [smul_smul, mv_smul]
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, _, mv_int_of_hom h h' hA i j, rfl⟩
  | zero => rw [smul_zero, mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add, mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, smul_comm, mv_smul]
    exact mul_mem_IhE (inc_int o) hu

theorem pt_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem pt_neg (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt, embV, tor0]

theorem mv_neg (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (-z) = -mv g g' z := by
  rw [← neg_one_smul D.host.E z, mv_smul, map_neg, map_one, neg_one_smul]

end GlobalTheory.NormSum.MovedTheta


open GlobalTheory.NormSum.MovedTheta in
theorem GlobalTheory.NormSum.exists_pt_of_mem_La_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  intro D hG cc δ _ N N' g g' L L' h h' x hx
  let P : VC D N N' → Prop := fun x => ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧
    ∀ i j, mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z i j ∈ IhE D cc
  have h0 : P 0 := ⟨0, (pt_zero cc δ).symm, fun i j => by rw [mv_zero]; exact zero_mem _⟩
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z + w, (pt_add cc δ z w).symm, fun i j => by rw [mv_add]; exact add_mem (hz i j) (hw i j)⟩
  have hneg : ∀ u, P u → P (-u) := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨-z, (pt_neg cc δ z).symm, fun i j => by rw [mv_neg]; exact neg_mem (hz i j)⟩
  show P x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨((c : D.host.K) : D.host.E) • A, ?_, mv_mem_IhE h h' hc hA⟩
      funext τ i j
      have e := hG.1 τ (c : D.host.K)
      simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [e, mul_assoc]
    | zero => rw [zero_smul]; exact h0
    | add u v _ _ hu hv => rw [add_smul]; exact hadd _ _ hu hv
    | neg u _ hu => rw [neg_smul]; exact hneg _ hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd _ _ hu hv
  | neg u _ hu => exact hneg _ hu
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.Vacuum.Parity

theorem zmod_two : ∀ a b c f r s p q : ZMod 2, a * a + b * c = a → a * b + b * f = b → c * a + f * c = c →
    c * b + f * f = f → ¬ (r * a + s * c = 0 ∧ r * b + s * f = 0) →
    ¬ (r - (r * a + s * c) = 0 ∧ s - (r * b + s * f) = 0) →
    (((p * b + q * f) * p - (p * a + q * c) * q) + (q * r - p * s) = 0 ↔ p = 0 ∧ q = 0) := by
  decide

theorem int_two (a b c f r s p q n e : ℤ) (he : e * e = 1) (h1 : a * a + b * c = a - 2 * n) (h2 : a * b + b * f = b)
    (h3 : c * a + f * c = c) (h4 : c * b + f * f = f - 2 * n)
    (h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)))
    (h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f)))) :
    Even (e * ((p * b + q * f) * p - (p * a + q * c) * q) + e * (q * r - p * s)) ↔ Even p ∧ Even q := by
  have he' : ¬ Even e := by
    intro h
    have : Even (e * e) := h.mul_right e
    rw [he] at this
    exact Int.not_even_one this
  rw [← mul_add, Int.even_mul, or_iff_right he']
  simp only [← ZMod.intCast_eq_zero_iff_even] at h5 h6 ⊢
  have two : (2 : ZMod 2) = 0 := rfl
  have g1 := congrArg (Int.cast : ℤ → ZMod 2) h1
  have g2 := congrArg (Int.cast : ℤ → ZMod 2) h2
  have g3 := congrArg (Int.cast : ℤ → ZMod 2) h3
  have g4 := congrArg (Int.cast : ℤ → ZMod 2) h4
  push_cast at g1 g2 g3 g4 h5 h6 ⊢
  rw [two, zero_mul, sub_zero] at g1 g4
  exact zmod_two _ _ _ _ _ _ _ _ g1 g2 g3 g4 h5 h6

theorem coord_unique (L : PeriodPair) {p q p' q' : ℤ}
    (h : (p : ℂ) * L.ω₁ + q * L.ω₂ = p' * L.ω₁ + q' * L.ω₂) : p = p' ∧ q = q' := by
  have hi := LinearIndependent.pair_iff.1 L.indep ((p : ℝ) - p') ((q : ℝ) - q') (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination h)
  exact ⟨by exact_mod_cast sub_eq_zero.1 hi.1, by exact_mod_cast sub_eq_zero.1 hi.2⟩

theorem half_mem_iff (L : PeriodPair) (p q : ℤ) :
    ((p : ℂ) * L.ω₁ + q * L.ω₂) / 2 ∈ L.lattice ↔ Even p ∧ Even q := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    have := coord_unique L (p := p) (q := q) (p' := m + m) (q' := n + n) (by
      push_cast
      linear_combination -2 * h)
    exact ⟨⟨m, this.1⟩, ⟨n, this.2⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    exact ⟨m, n, by push_cast; ring⟩

theorem exists_sign (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ p q r s : ℤ,
      gl3FieldFirst Λ ((p : ℂ) * L.ω₁ + q * L.ω₂) ((r : ℂ) * L.ω₁ + s * L.ω₂) = ((e * (q * r - p * s) : ℤ) : ℝ) := by
  have hd := GlobalTheory.PlaneLattice.signedArea_ne_zero L
  have ha := GlobalTheory.PlaneLattice.area_eq L Λ h
  have hpos : 0 < area Λ := ha ▸ abs_pos.2 hd
  obtain ⟨e, he, he2⟩ : ∃ e : ℤ, area Λ = e * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ∧ e * e = 1 := by
    rcases abs_choice ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with h' | h'
    · exact ⟨1, by rw [ha, h']; simp only [Int.cast_one, one_mul], by simp⟩
    · exact ⟨-1, by rw [ha, h']; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul], by simp⟩
  refine ⟨e, he2, fun p q r s => ?_⟩
  have he3 : (e : ℝ) * e = 1 := by exact_mod_cast he2
  rw [gl3FieldFirst, div_eq_iff hpos.ne', he]
  simp
  linear_combination (-((q : ℝ) * r - p * s) * (L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re)) * he3

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  rw [q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
  simp [← Complex.ofReal_pow]
  ring

theorem cm_generator_sq_quadratic_eq (D : D7) : ∃ n : ℤ, w0 D * w0 D = w0 D - 2 * n := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, D.host.d + 1 = 8 * n := ⟨(D.host.d + 1) / 8, by omega⟩
  have hn' : (D.host.d : ℂ) + 1 = 8 * n := by exact_mod_cast hn
  have hs : (Real.sqrt D.host.d : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  refine ⟨n, ?_⟩
  rw [w0]
  push_cast
  linear_combination (Real.sqrt D.host.d : ℂ) ^ 2 / 4 * Complex.I_sq - 1 / 4 * hs - 1 / 4 * hn'

theorem lamOf_stable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) :
    ∀ w ∈ lamOf D cc δ, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, by simp; ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem lamOf_eq_closure (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  refine ⟨L.ω₁, L.ω₂, L.indep, AddSubgroup.ext fun z => ?_⟩
  rw [hL, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp only [zsmul_eq_mul]

theorem even_im_hermitian_sub : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → t0 ∉ (lamOf D cc δ) ∧ ∀ ω ∈ (lamOf D cc δ), ∃ m k : ℤ, q1 D (lamOf D cc δ) ω = m ∧ gl3FieldFirst (lamOf D cc δ) ω (2 * t0) = k ∧ (Even (m + k) ↔ ω / 2 ∈ (lamOf D cc δ)) := by
  intro D _ cc δ hc t0 ht
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  obtain ⟨α, hα⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hst : ∀ w ∈ lamOf D cc δ, w0 D * w ∈ lamOf D cc δ := fun w hw =>
    hα ▸ lamOf_stable D cc δ α w hw
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨fun h0 => ht2 (hst _ h0), fun ω hω => ?_⟩
  obtain ⟨e, he, hE⟩ := exists_sign L _ hL
  obtain ⟨n, hn⟩ := cm_generator_sq_quadratic_eq D
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₁_mem_lattice)))
  obtain ⟨c, f, hcf⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₂_mem_lattice)))
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ht1)
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((hL _).1 hω)
  have h12 := coord_unique L (p := a * a + b * c) (q := a * b + b * f) (p' := a - 2 * n) (q' := b) (by
    push_cast
    linear_combination (a + w0 D - 1) * hab + b * hcf + L.ω₁ * hn)
  have h34 := coord_unique L (p := c * a + f * c) (q := c * b + f * f) (p' := c) (q' := f - 2 * n) (by
    push_cast
    linear_combination c * hab + (f + w0 D - 1) * hcf + L.ω₂ * hn)
  have h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht2
    convert h using 1
    change w0 D * t0 = _
    push_cast
    linear_combination (-1 / 2 * r) * hab - 1 / 2 * s * hcf - 1 / 2 * w0 D * hrs
  have h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f))) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht3
    convert h using 1
    have e1 : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - w0 D := by rw [w0]; ring
    rw [e1]
    push_cast
    linear_combination (1 / 2 * r) * hab + 1 / 2 * s * hcf - 1 / 2 * (1 - w0 D) * hrs
  have hw : w0 D * ((p : ℂ) * L.ω₁ + q * L.ω₂) =
      ((p * a + q * c : ℤ) : ℂ) * L.ω₁ + ((p * b + q * f : ℤ) : ℂ) * L.ω₂ := by
    push_cast
    linear_combination -p * hab - q * hcf
  refine ⟨e * ((p * b + q * f) * p - (p * a + q * c) * q), e * (q * r - p * s), ?_, ?_, ?_⟩
  · rw [cmQuadraticForm_eq_alternatingForm, hw, hE]
  · rw [← hrs, hE]
  · rw [hL, half_mem_iff]
    exact int_two a b c f r s p q n e he h12.1 h12.2 h34.1 h34.2 h5 h6

end GlobalTheory.Vacuum.Parity
end
