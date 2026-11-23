module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.TraceSkew

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toAlgHom.toRingHom

lemma map_cc_mul {r : ℕ} (A B : Matrix (Fin r) (Fin r) E) :
    (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := ccHom E)

lemma exists_ne_zero_cc_eq_neg : ∃ β : E, β ≠ 0 ∧ cc β = -β := by
  by_contra h
  push_neg at h
  apply IsCMField.complexConj_ne_one E
  refine AlgEquiv.ext fun x => ?_
  have h1 : cc (x - cc x) = -(x - cc x) := by
    simp only [cc, map_sub, IsCMField.complexConj_apply_apply]; ring
  have h2 := h (x - cc x)
  have h3 : x - cc x = 0 := by
    by_contra hne
    exact h2 hne h1
  have : cc x = x := by linear_combination -h3
  simpa [cc] using this

lemma herm_eq_dot {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma form_skew_of_matrix {r : ℕ} (G Y : Matrix (Fin r) (Fin r) E)
    (h : Yᵀ * G + G * Y.map cc = 0) (u w : Fin r → E) :
    herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0 := by
  have hc : (fun b => cc ((Y *ᵥ w) b)) = Y.map cc *ᵥ (fun b => cc (w b)) := by
    funext b

    simp [mulVec, dotProduct, cc, map_sum, map_mul]
  rw [herm_eq_dot, herm_eq_dot, hc, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, h, zero_mulVec, dotProduct_zero]

end GlobalTheory.TraceSkew

namespace GlobalTheory.TraceSkew

theorem traceForm_nondegenerate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ Y : Matrix (Fin r) (Fin r) E, Y.trace = 0 → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace = 0) → X = 0 := by
  intro E _ _ _ r G X hG hdet htr _hX hY
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    ext i
    exact i.elim0
  have hr : (r : E) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGTu : IsUnit Gᵀ.det := by rw [det_transpose]; exact hGu
  set Q : Matrix (Fin r) (Fin r) E := (Gᵀ)⁻¹ with hQdef
  have hQT : Qᵀ * G = 1 := by
    rw [hQdef, transpose_nonsing_inv, transpose_transpose]
    exact nonsing_inv_mul G hGu
  have hQG : Q * Gᵀ = 1 := nonsing_inv_mul _ hGTu
  have hGmap : Gᵀ.map cc = G := by
    ext a b
    simp only [map_apply, transpose_apply]
    exact hG b a
  have hQmap : G * Q.map cc = 1 := by
    have h1 : Q.map cc * G = 1 := by
      rw [← hGmap, ← map_cc_mul, hQG]
      ext a b
      simp [map_apply, Matrix.one_apply, cc]
    exact mul_eq_one_comm.mp h1

  have hskew : ∀ K : Matrix (Fin r) (Fin r) E, Kᵀ + K.map cc = 0 →
      (Q * K)ᵀ * G + G * (Q * K).map cc = 0 := by
    intro K hK
    rw [transpose_mul, map_cc_mul, Matrix.mul_assoc, hQT, Matrix.mul_one, ← Matrix.mul_assoc,
      hQmap, Matrix.one_mul]
    exact hK

  have htrskew : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 →
      cc Y.trace = -Y.trace := by
    intro Y hY'
    have h0 : G * Y.map cc = -(Yᵀ * G) := eq_neg_of_add_eq_zero_right hY'
    have h1 : Y.map cc = -(G⁻¹ * (Yᵀ * G)) := by
      calc Y.map cc = G⁻¹ * (G * Y.map cc) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul G hGu, Matrix.one_mul]
        _ = -(G⁻¹ * (Yᵀ * G)) := by rw [h0, Matrix.mul_neg]
    have h2 : (Y.map cc).trace = cc Y.trace := by

      simp [trace, cc, map_sum]
    rw [← h2, h1, trace_neg, trace_mul_comm, Matrix.mul_assoc, mul_nonsing_inv G hGu,
      Matrix.mul_one, trace_transpose]

  have hXY : ∀ Y : Matrix (Fin r) (Fin r) E, Yᵀ * G + G * Y.map cc = 0 → (X * Y).trace = 0 := by
    intro Y hY'
    set c : E := Y.trace / r with hcdef
    have hc : cc c = -c := by
      have : cc (r : E) = r := map_natCast (ccHom E) r
      rw [hcdef, show cc (Y.trace / r) = cc Y.trace / cc (r : E) from map_div₀ (ccHom E) _ _,
        this, htrskew Y hY', neg_div]
    have hmap1 : (c • (1 : Matrix (Fin r) (Fin r) E)).map cc = -(c • 1) := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [Matrix.one_apply, hc]
      · simp [Matrix.one_apply, hab, cc]
    have hmapY : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = Y.map cc - (c • (1 : Matrix (Fin r) (Fin r) E)).map cc := by
      ext a b
      simp [cc]
    have hs : (Y - c • (1 : Matrix (Fin r) (Fin r) E))ᵀ * G + G * (Y - c • (1 : Matrix (Fin r) (Fin r) E)).map cc = 0 := by
      rw [hmapY, hmap1, transpose_sub, transpose_smul, transpose_one, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, ← hY']
      abel
    have ht : (Y - c • (1 : Matrix (Fin r) (Fin r) E)).trace = 0 := by
      rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hcdef,
        div_mul_cancel₀ _ hr, sub_self]
    have h := hY (Y - c • (1 : Matrix (Fin r) (Fin r) E)) ht (form_skew_of_matrix G _ hs)
    rw [Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul, htr,
      smul_zero, sub_zero] at h
    exact h

  obtain ⟨β, hβ0, hβ⟩ := exists_ne_zero_cc_eq_neg (E := E)
  have hβ' : IsCMField.complexConj E β = -β := hβ
  have hall : ∀ K : Matrix (Fin r) (Fin r) E, (X * Q * K).trace = 0 := by
    intro K
    let A : Matrix (Fin r) (Fin r) E := of fun i j => (K i j - cc (K j i)) / 2
    let B : Matrix (Fin r) (Fin r) E := of fun i j => (K i j + cc (K j i)) / (2 * β)
    have hA : Aᵀ + A.map cc = 0 := by
      ext i j
      simp only [A, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_sub,
        map_div₀, map_ofNat, IsCMField.complexConj_apply_apply]
      ring
    have hB : Bᵀ + B.map cc = 0 := by
      ext i j
      simp only [B, Matrix.add_apply, transpose_apply, map_apply, of_apply, Matrix.zero_apply, cc, map_add (f := _),
        map_div₀, map_mul, map_ofNat, IsCMField.complexConj_apply_apply, hβ']
      field_simp
      ring
    have hK : K = A + β • B := by
      ext i j
      simp only [A, B, Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
      field_simp
      ring
    rw [Matrix.mul_assoc, hK, Matrix.mul_add, Matrix.mul_add, trace_add, Matrix.mul_smul,
      Matrix.mul_smul, trace_smul, hXY _ (hskew A hA), hXY _ (hskew B hB), smul_zero, add_zero]
  have hXQ : X * Q = 0 := by
    rw [ext_iff_trace_mul_right]
    intro K
    rw [hall K, Matrix.zero_mul, trace_zero]
  calc X = X * Q * Gᵀ := by rw [Matrix.mul_assoc, hQG, Matrix.mul_one]
    _ = 0 := by rw [hXQ, Matrix.zero_mul]

end GlobalTheory.TraceSkew
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArithIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def moveLin (δ : GL (Fin r) E) : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) :=
  ((δ : Matrix (Fin r) (Fin r) E).mulVecLin).restrictScalars (𝓞 E)

omit [IsCMField E] in
theorem moveLin_apply (δ : GL (Fin r) E) (v : Fin r → E) :
    moveLin δ v = (δ : Matrix (Fin r) (Fin r) E).mulVec v := rfl

omit [NumberField E] [IsCMField E] in
theorem inv_mulVec_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
      ((δ : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in
theorem mulVec_inv_mulVec (δ : GL (Fin r) E) (v : Fin r → E) :
    (δ : Matrix (Fin r) (Fin r) E).mulVec
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

omit [IsCMField E] in
theorem mem_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (y : Fin r → E) :
    y ∈ L.map (moveLin δ) ↔
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [moveLin_apply, inv_mulVec_mulVec]
    exact hx
  · intro h
    exact ⟨_, h, by rw [moveLin_apply, mulVec_inv_mulVec]⟩

omit [IsCMField E] in
theorem span_map_moveLin (δ : GL (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E))
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span E ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) = ⊤ := by
  have hsurj : Function.Surjective (δ : Matrix (Fin r) (Fin r) E).mulVecLin := fun y =>
    ⟨_, mulVec_inv_mulVec δ y⟩
  have : ((L.map (moveLin δ) : Submodule (𝓞 E) (Fin r → E)) : Set (Fin r → E)) =
      (δ : Matrix (Fin r) (Fin r) E).mulVecLin '' (L : Set (Fin r → E)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, ← Submodule.map_span, hL, Submodule.map_top, LinearMap.range_eq_top]
  exact hsurj

theorem isUStab_conj (X₂ X : Data E r) (δ : GL (Fin r) E) (hG : X₂.Gm = X.Gm)
    (hδ : ∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hK : ∀ x, x ∈ X₂.Λ.map (moveLin δ) ↔
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ X₂.Λ.map (moveLin δ)) :
    IsUStab X₂.Gm X₂.Λ (δ⁻¹ * γ * δ) := by
  have hval : ∀ x, (((δ⁻¹ * γ * δ : GL (Fin r) E)) : Matrix (Fin r) (Fin r) E).mulVec x =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec
        ((γ : Matrix (Fin r) (Fin r) E).mulVec ((δ : Matrix (Fin r) (Fin r) E).mulVec x)) := by
    intro x
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [hval, hval, ← hδ, mulVec_inv_mulVec, mulVec_inv_mulVec, hG, (X.Γ_stab γ hγ).1, ← hG, hδ]
  · rw [hval, ← mem_map_moveLin, ← hK, mem_map_moveLin, inv_mulVec_mulVec]


omit [NumberField E] [IsCMField E] in
theorem relIndex_ne_zero_of_reps (Γ₂ A : Subgroup (GL (Fin r) E)) (δ : GL (Fin r) E)
    (S : Finset (GL (Fin r) E))
    (h : ∀ γ ∈ A, ∃ s ∈ S, s⁻¹ * (δ⁻¹ * γ * δ) ∈ Γ₂) :
    (Γ₂.map (MulAut.conj δ).toMonoidHom).relIndex A ≠ 0 := by
  classical
  set H := Γ₂.map (MulAut.conj δ).toMonoidHom with hH
  choose! f hfS hf using h
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    refine Finite.of_injective
      (fun q : A ⧸ H.subgroupOf A => (⟨f (q.out : A), hfS _ q.out.2⟩ : S)) ?_
    intro p q hpq
    have hpq' : f (p.out : A) = f (q.out : A) := congrArg Subtype.val hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have ha := hf _ p.out.2
    have hb := hf _ q.out.2
    rw [hpq'] at ha
    have hc := Γ₂.mul_mem (Γ₂.inv_mem ha) hb
    refine ⟨_, hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_map_conj_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ : GL (Fin r) E), X₂.Gm = X.Gm → (∀ v w, herm X₂.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X₂.Gm v w) → (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0 := by
  intro E _ _ _ r X₂ X δ hG hδ
  set Λ' := X₂.Λ.map (moveLin δ) with hΛ'
  have hfg : Λ'.FG := X₂.Λ_fg.map _
  have hsp := span_map_moveLin δ X₂.Λ X₂.Λ_span
  obtain ⟨n₁, hn₁, h₁⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice X.Λ Λ' hfg X.Λ_span
  obtain ⟨n₂, hn₂, h₂⟩ := GlobalTheory.T.exists_pos_nat_smul_mem_of_fg_and_spanning_lattice Λ' X.Λ X.Λ_fg hsp
  have hnat : ∀ (L : Submodule (𝓞 E) (Fin r → E)) (k : ℕ) (v : Fin r → E), v ∈ L →
      (k : E) • v ∈ L := by
    intro L k v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv k
  have hA : ∀ v ∈ Λ', ((n₁ * n₂ : ℕ) : E) • v ∈ X.Λ := by
    intro v hv
    have := hnat _ n₂ _ (h₁ v hv)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm n₂] at this
  have hB : ∀ v ∈ X.Λ, ((n₁ * n₂ : ℕ) : E) • v ∈ Λ' := by
    intro v hv
    have := hnat _ n₁ _ (h₂ v hv)
    rwa [smul_smul, ← Nat.cast_mul] at this
  obtain ⟨K, hK, hKΛ⟩ := GlobalTheory.T.exists_finite_relIndex_stabilizer_commensurable_lattice X.Λ Λ' (n₁ * n₂) (Nat.mul_pos hn₁ hn₂) X.Λ_fg hA hB X.Γ
    (fun γ hγ => (X.Γ_stab γ hγ).2)
  obtain ⟨S, hS⟩ := X₂.Γ_index
  have hAH : (X₂.Γ.map (MulAut.conj δ).toMonoidHom).relIndex (X.Γ ⊓ K) ≠ 0 :=
    relIndex_ne_zero_of_reps X₂.Γ (X.Γ ⊓ K) δ S fun γ hγ =>
      hS _ (isUStab_conj X₂ X δ hG hδ hγ.1 (hKΛ γ hγ.2))
  refine Subgroup.relIndex_ne_zero_trans hAH ?_
  rwa [Subgroup.inf_relIndex_left]

end GlobalTheory.ArithIndex
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

def TrivCond {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S) : Prop :=
  ∀ (Y : Scheme.{0}) (φ : Y ⟶ A.left) (y : Y ⟶ T), IsPullback φ y A.hom t →
    ∃ s : (N.pull φ).Gen, s.IsGen

theorem exists_gen_pull_comp {X Y Y' : Scheme.{0}} (N : LB X) (φ : Y ⟶ X)
    (h : Y' ⟶ Y) (hs : ∃ s : (N.pull φ).Gen, s.IsGen) : ∃ s : (N.pull (h ≫ φ)).Gen, s.IsGen := by
  obtain ⟨s, hs⟩ := hs
  exact ⟨LB.pullGen N (fun _ => φ) (fun _ => 1) s h, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ s hs h⟩

theorem trivCond_comp {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T T' : Scheme.{0}) (t : T ⟶ S)
    (u : T' ⟶ T) (h : TrivCond A N T t) : TrivCond A N T' (u ≫ t) := by
  intro Y φ y hY
  have hw : φ ≫ A.hom = (y ≫ u) ≫ t := by rw [hY.w, Category.assoc]
  have := exists_gen_pull_comp N _ (pullback.lift φ (y ≫ u) hw)
    (h _ _ _ (IsPullback.of_hasPullback A.hom t))
  rwa [pullback.lift_fst] at this

theorem trivCond_iff {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S)
    (X : Scheme.{0}) (φ' : X ⟶ A.left) (x : X ⟶ T) (hP : IsPullback φ' x A.hom t) :
    (∃ s : (N.pull φ').Gen, s.IsGen) ↔ TrivCond A N T t := by
  refine ⟨fun h Y φ y hY => ?_, fun h => h _ _ _ hP⟩
  have := exists_gen_pull_comp N φ' (hP.lift φ y hY.w) h
  rwa [hP.lift_fst] at this

end GlobalTheory.TrivLocus
end
