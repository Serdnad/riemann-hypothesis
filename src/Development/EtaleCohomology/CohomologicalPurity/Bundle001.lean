module

public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef
import Mathlib.Algebra.Category.Ring.FilteredColimits
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style

@[expose] public section

section

noncomputable section
open scoped TensorProduct

namespace LateralTheory.CohomologicalPurity.Hz

theorem coeq_elem {A S S' : Type} [CommRing A] [CommRing S] [CommRing S'] (φ : A →+* S) (φ' : A →+* S')
    (I : Ideal A) (u v : S →+* S') (hφ : Good φ I) (hu : u.comp φ = φ') (hv : v.comp φ = φ') :
    ∃ e : S', (∀ s, (v s - u s) * e = 0) ∧ e - 1 ∈ I.map φ' := by
  let := φ.toAlgebra
  let := φ'.toAlgebra
  have : Algebra.Etale A S := hφ.etale
  let u' : S →ₐ[A] S' := { u with commutes' := fun a => RingHom.congr_fun hu a }
  let v' : S →ₐ[A] S' := { v with commutes' := fun a => RingHom.congr_fun hv a }
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := S)).1 inferInstance
  refine ⟨Algebra.TensorProduct.productMap u' v' t, fun s => ?_, ?_⟩
  · have h := congrArg (Algebra.TensorProduct.productMap u' v') (ht1 s)
    simpa [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul, u', v'] using h
  · have hmem : ∀ x ∈ I.map φ, u x ∈ I.map φ' ∧ v x ∈ I.map φ' := fun x hx => by
      refine ⟨?_, ?_⟩
      · have := Ideal.mem_map_of_mem u hx
        rwa [Ideal.map_map, hu] at this
      · have := Ideal.mem_map_of_mem v hx
        rwa [Ideal.map_map, hv] at this
    let q := Ideal.Quotient.mkₐ A (I.map φ')
    have hqv : q.comp v' = q.comp u' := by
      ext s
      obtain ⟨a, ha⟩ := hφ.surj s
      have e1 : v s - u s = v (s - φ a) - u (s - φ a) := by
        have h1 : v (φ a) = u (φ a) := (RingHom.congr_fun hv a).trans (RingHom.congr_fun hu a).symm
        rw [map_sub, map_sub, h1]; ring
      change Ideal.Quotient.mk _ (v s) = Ideal.Quotient.mk _ (u s)
      rw [Ideal.Quotient.eq, e1]
      exact Ideal.sub_mem _ (hmem _ ha).2 (hmem _ ha).1
    have hprod : q.comp (Algebra.TensorProduct.productMap u' v') = q.comp (u'.comp (Algebra.TensorProduct.lmul' A)) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      have hb := AlgHom.congr_fun hqv b
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        Algebra.TensorProduct.lmul'_apply_tmul] at hb ⊢
      rw [hb]
    have h := AlgHom.congr_fun hprod t
    simp only [AlgHom.comp_apply] at h
    rw [ht2, map_one] at h
    rw [← Ideal.Quotient.eq]
    simpa [q] using h

theorem LeafCoeq_of (hInv : LeafInv) (hComp : LeafComp) : LeafCoeq := by
  intro A S S' _ _ _ φ φ' I u v hφ hφ' hu hv
  obtain ⟨e, he1, he2⟩ := coeq_elem φ φ' I u v hφ hu hv
  obtain ⟨T, _, ψ, hg, hunit⟩ := hInv S' (I.map φ') (e - 1) he2
  rw [add_sub_cancel] at hunit
  refine ⟨T, inferInstance, ψ, RingHom.ext fun s => ?_, hComp.2 A S' T φ' ψ I hφ' hg⟩
  have h := congrArg ψ (he1 s)
  rw [map_mul, map_zero, hunit.mul_left_eq_zero, map_sub, sub_eq_zero] at h
  exact h.symm

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

theorem evalMapHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (x : R) :
    (p.map f).eval (f x) = f (p.eval x) := by
  rw [eval_map, eval₂_at_apply]

theorem Diag.leg_comp_map {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J}
    (e : j ⟶ k) : (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem LeafColHens_of (hS : LeafStage) (hI : LeafInv) (hR : LeafRoot) : LeafColHens := by
  classical
  intro A _ I Δ c hc η hη
  have st := hS A I Δ c hc η hη
  have push : ∀ j (S : Type) [CommRing S] (φ : Δ.D.obj j →+* S), Good φ (I.map (Δ.s j)) →
      ∃ π : S →+* c.pt, π.comp φ = Δ.leg c j := by
    intro j S _ φ hφ
    obtain ⟨k, e, ρ, hρ⟩ := Δ.exh j S φ hφ
    exact ⟨(Δ.leg c k).comp ρ, by rw [RingHom.comp_assoc, hρ, Δ.leg_comp_map]⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [Ring.mem_jacobson_iff]
    intro y
    have hzy : z * y ∈ I.map η := Ideal.mul_mem_right y _ hz
    obtain ⟨j, hj⟩ := st.1 {z * y}
    obtain ⟨x, hx⟩ := hj (z * y) (Finset.mem_singleton_self _)
    have hx' : x ∈ I.map (Δ.s j) := st.2 j x (by rw [hx]; exact hzy)
    obtain ⟨S, _, φ, hφ, hu⟩ := hI (Δ.D.obj j) (I.map (Δ.s j)) x hx'
    obtain ⟨π, hπ⟩ := push j S φ hφ
    have h := hu.map π
    rw [← RingHom.comp_apply, hπ, map_add (f := _), map_one, hx, add_comm] at h
    exact h
  · intro f hf a₀ ha₀ hu
    obtain ⟨u, hu'⟩ := Ideal.Quotient.mk_surjective (↑hu.unit⁻¹ : c.pt ⧸ I.map η)
    have hdu : f.derivative.eval a₀ * u - 1 ∈ I.map η := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu', map_one, IsUnit.mul_val_inv, sub_self]
    let T : Finset c.pt := insert a₀ (insert u (f.support.image f.coeff))
    obtain ⟨j, hj⟩ := st.1 T
    obtain ⟨a, ha⟩ := hj a₀ (Finset.mem_insert_self _ _)
    obtain ⟨v, hv⟩ := hj u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hco : ∀ n, f.coeff n ∈ Set.range (Δ.leg c j) := by
      intro n
      by_cases hn : n ∈ f.support
      · exact hj _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
      · exact ⟨0, by rw [map_zero, notMem_support_iff.1 hn]⟩
    obtain ⟨g, hg, -, hgm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hco) hf
    have h1 : g.eval a ∈ I.map (Δ.s j) := st.2 j _ (by rw [← evalMapHom, hg, ha]; exact ha₀)
    have h2 : g.derivative.eval a * v - 1 ∈ I.map (Δ.s j) := st.2 j _ (by
      rw [map_sub, map_mul, map_one, ← evalMapHom, ← derivative_map, hg, ha, hv]; exact hdu)
    have h3 : IsUnit (Ideal.Quotient.mk (I.map (Δ.s j)) (g.derivative.eval a)) :=
      IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v)
        (by rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (Δ.s j)))]; exact Ideal.Quotient.eq.2 h2)
    obtain ⟨S, _, φ, b, hφ, hb, hba⟩ := hR (Δ.D.obj j) (I.map (Δ.s j)) g a hgm h1 h3
    obtain ⟨π, hπ⟩ := push j S φ hφ
    refine ⟨π b, ?_, ?_⟩
    · have h := hb.map (f := π)
      rwa [Polynomial.map_map, hπ, hg] at h
    · have h := Ideal.mem_map_of_mem π hba
      rw [Ideal.map_map, Ideal.map_map, hπ, hη, map_sub, ← RingHom.comp_apply, hπ, ha] at h
      exact h

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz.DiagPf

variable {A : Type} [CommRing A] (I : Ideal A)

structure Obj where
  n : ℕ
  K : Ideal (MvPolynomial (Fin n) A)
  good : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ K)) I

variable {I}

abbrev Obj.Q (X : Obj I) : Type := MvPolynomial (Fin X.n) A ⧸ X.K

abbrev Obj.s (X : Obj I) : A →+* X.Q := algebraMap A X.Q

instance : SmallCategory (Obj I) where
  Hom X Y := {f : X.Q →+* Y.Q // f.comp X.s = Y.s}
  id X := ⟨RingHom.id _, RingHom.id_comp _⟩
  comp f g := ⟨g.1.comp f.1, by rw [RingHom.comp_assoc, f.2, g.2]⟩
  id_comp f := Subtype.ext (RingHom.comp_id _)
  comp_id f := Subtype.ext (RingHom.id_comp _)
  assoc f g h := Subtype.ext (RingHom.comp_assoc _ _ _).symm

def DF : Obj I ⥤ CommRingCat.{0} where
  obj X := CommRingCat.of X.Q
  map f := CommRingCat.ofHom f.1
  map_id _ := rfl
  map_comp _ _ := rfl

theorem key (hC : LeafComp) {T : Type} [CommRing T] (φ : A →+* T) (h : Good φ I) :
    ∃ (X : Obj I) (ρ : T →+* X.Q), ρ.comp φ = X.s := by
  let _ := φ.toAlgebra
  have : Algebra.Etale A T := h.etale
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType A T)
  let e0 := Ideal.quotientKerAlgEquivOfSurjective hf
  have hcomp : (e0.symm : T →+* MvPolynomial (Fin n) A ⧸ RingHom.ker f).comp φ =
      algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) := by
    have := AlgHom.comp_algebraMap (e0.symm : T →ₐ[A] MvPolynomial (Fin n) A ⧸ RingHom.ker f)
    rw [← RingHom.algebraMap_toAlgebra φ]
    exact this
  have hg : Good (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker f)) I := by
    rw [← hcomp]
    exact hC.2 _ _ _ _ _ _ h (hC.1 _ _ e0.symm.toRingEquiv _)
  exact ⟨⟨n, RingHom.ker f, hg⟩, e0.symm, hcomp⟩

theorem diag_nonempty (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) (A : Type) [CommRing A] (I : Ideal A) :
    Nonempty (Diag A I) := by
  have hf : IsFiltered (Obj I) :=
    { cocone_objs := fun X Y => by
        obtain ⟨T, _, u, u', huu, hg⟩ := hS _ _ _ X.s Y.s I X.good Y.good
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp u, by rw [RingHom.comp_assoc, hρ]⟩, ⟨ρ.comp u', ?_⟩, trivial⟩
        rw [RingHom.comp_assoc, ← huu, hρ]
      cocone_maps := fun X Y f g => by
        obtain ⟨T, _, w, hw, hg⟩ := hQ _ _ _ X.s Y.s I f.1 g.1 X.good Y.good f.2 g.2
        obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
        refine ⟨Z, ⟨ρ.comp w, by rw [RingHom.comp_assoc, hρ]⟩, Subtype.ext ?_⟩
        change (ρ.comp w).comp f.1 = (ρ.comp w).comp g.1
        rw [RingHom.comp_assoc, RingHom.comp_assoc, hw]
      nonempty := by
        obtain ⟨Z, _, _⟩ := key hC (RingHom.id A) (hC.1 A A (RingEquiv.refl A) I)
        exact ⟨Z⟩ }
  refine ⟨@Diag.mk A _ I (Obj I) _ hf DF (fun X => X.s) (fun e => e.2) (fun X => X.good) ?_⟩
  intro j S _ ψ hψ
  have hg : Good (ψ.comp j.s) I := hC.2 _ _ _ _ _ _ j.good hψ
  obtain ⟨Z, ρ, hρ⟩ := key hC _ hg
  exact ⟨Z, ⟨ρ.comp ψ, hρ⟩, ρ, rfl⟩

end LateralTheory.CohomologicalPurity.Hz.DiagPf

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafDiag_of (hC : LeafComp) (hS : LeafSup) (hQ : LeafCoeq) : LeafDiag :=
  fun A _ I => DiagPf.diag_nonempty hC hS hQ A I

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section
open Polynomial

namespace LateralTheory.CohomologicalPurity.Hz

def LeafRootStd : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ (S : Type) (_ : CommRing S) (φ : A →+* S) (b : S), φ.Etale ∧
    (∃ r : S →+* A ⧸ I, r.comp φ = Ideal.Quotient.mk I) ∧ (∀ s : S, ∃ a' : A, s - φ a' ∈ I.map φ) ∧
    (f.map φ).IsRoot b ∧ b - φ a ∈ I.map φ ∧
    (∀ (B : Type) [CommRing B] (χ₁ χ₂ : S →+* B), χ₁.comp φ = χ₂.comp φ → χ₁ b = χ₂ b → χ₁ = χ₂) ∧
    (∀ (B : Type) [CommRing B] (ψ : A →+* B) (c : B), (f.map ψ).IsRoot c →
      IsUnit ((f.derivative.map ψ).eval c) → IsUnit (((f /ₘ (X - C a)).map ψ).eval c) →
      ∃ χ : S →+* B, χ.comp φ = ψ ∧ χ b = c)

def LeafRootHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B), HenselianRing B J →
  ∀ (ψ : A →+* B), I ≤ J.comap ψ → ∀ (f : A[X]) (a : A), f.Monic → f.eval a ∈ I →
  IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) →
  ∃ c : B, (f.map ψ).IsRoot c ∧ c - ψ a ∈ J ∧ IsUnit ((f.derivative.map ψ).eval c) ∧
    IsUnit (((f /ₘ (X - C a)).map ψ).eval c) ∧ ∀ c' : B, (f.map ψ).IsRoot c' → c' - ψ a ∈ J → c' = c

theorem LeafRoot_of (h1 : LeafRootStd) (h2 : LeafRootHens) : LeafRoot := by
  intro A _ I f a hf hfa hu
  obtain ⟨S, _, φ, b, he, hr, hs, hb, hba, hext, hlift⟩ := h1 A I f a hf hfa hu
  refine ⟨S, inferInstance, φ, b, ⟨he, hr, hs, ?_⟩, hb, hba⟩
  intro B _ J hJ ψ hIJ
  obtain ⟨c, hc, _, hc1, hc2, huniq⟩ := h2 A B I J hJ ψ hIJ f a hf hfa hu
  obtain ⟨χ, hχ, hχb⟩ := hlift B ψ c hc hc1 hc2
  refine ⟨χ, hχ, fun χ' hχ' => hext B χ' χ (hχ'.trans hχ.symm) ?_⟩
  rw [hχb]
  have hpa : χ' (φ a) = ψ a := by rw [← hχ']; rfl
  apply huniq
  · have h4 : (f.map φ).map χ' = f.map ψ := by rw [Polynomial.map_map, hχ']
    rw [← h4]
    exact Polynomial.IsRoot.map χ' hb
  · have h3 : (I.map φ).map χ' ≤ J := by
      rw [Ideal.map_map, hχ', Ideal.map_le_iff_le_comap]; exact hIJ
    have h5 := h3 (Ideal.mem_map_of_mem χ' hba)
    rwa [map_sub, hpa] at h5

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Diag.leg_w {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J} (e : j ⟶ k) :
    (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem Good.kill {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A}
    (ψ : S →+* A ⧸ I) (hψ : ψ.comp φ = Ideal.Quotient.mk I) : ∀ y ∈ I.map φ, ψ y = 0 := by
  intro y hy
  have h : I.map φ ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ψ (φ a) = 0
    rw [← RingHom.comp_apply, hψ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  exact h hy

theorem Good.retr_unique {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I)
    (χ χ' : S →+* A ⧸ I) (hχ : χ.comp φ = Ideal.Quotient.mk I) (hχ' : χ'.comp φ = Ideal.Quotient.mk I) : χ = χ' := by
  refine RingHom.ext fun s => ?_
  obtain ⟨a, ha⟩ := h.surj s
  have e1 := Good.kill χ hχ _ ha
  have e2 := Good.kill χ' hχ' _ ha
  rw [map_sub, sub_eq_zero] at e1 e2
  rw [e1, e2, ← RingHom.comp_apply, hχ, ← RingHom.comp_apply, hχ']

theorem stage_fin {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (T : Finset c.pt) : ∃ j, ∀ t ∈ T, t ∈ (Δ.leg c j).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨(IsFiltered.nonempty : Nonempty Δ.J).some, by simp⟩
  | insert x T hx ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep Δ.D hc x
    refine ⟨IsFiltered.max j k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · refine ⟨(Δ.D.map (IsFiltered.rightToMax j k)).hom y, ?_⟩
      rw [← RingHom.comp_apply, Δ.leg_w]
      exact hy
    · obtain ⟨z, rfl⟩ := hj t ht
      exact ⟨(Δ.D.map (IsFiltered.leftToMax j k)).hom z, by rw [← RingHom.comp_apply, Δ.leg_w]⟩

theorem stage_ideal {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (η : A →+* c.pt) (hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = η) (j : Δ.J) (x : Δ.D.obj j)
    (hx : Δ.leg c j x ∈ I.map η) : x ∈ I.map (Δ.s j) := by
  let r : ∀ j, Δ.D.obj j →+* A ⧸ I := fun j => (Δ.good j).retr.choose
  have hr : ∀ j, (r j).comp (Δ.s j) = Ideal.Quotient.mk I := fun j => (Δ.good j).retr.choose_spec
  let cc : Cocone Δ.D :=
    { pt := CommRingCat.of (A ⧸ I)
      ι := { app := fun j => CommRingCat.ofHom (r j)
             naturality := fun j k e => by
               apply CommRingCat.hom_ext
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
                 CommRingCat.hom_ofHom]
               exact (Δ.good j).retr_unique _ _ (by rw [RingHom.comp_assoc, Δ.nat e, hr]) (hr j) } }
  let R : c.pt →+* A ⧸ I := (hc.desc cc).hom
  have hR : ∀ j, R.comp (Δ.leg c j) = r j := fun j => congrArg CommRingCat.Hom.hom (hc.fac cc j)
  have hRη : R.comp η = Ideal.Quotient.mk I := by rw [← hη j, ← RingHom.comp_assoc, hR, hr]
  obtain ⟨a, ha⟩ := (Δ.good j).surj x
  have h1 : Δ.leg c j (x - Δ.s j a) ∈ I.map η := by
    have := Ideal.mem_map_of_mem (Δ.leg c j) ha
    rwa [Ideal.map_map, hη] at this
  have h2 : η a ∈ I.map η := by
    have e : η a = Δ.leg c j x - Δ.leg c j (x - Δ.s j a) := by
      rw [map_sub, sub_sub_cancel, ← RingHom.comp_apply, hη]
    rw [e]
    exact Ideal.sub_mem _ hx h1
  have h3 : Ideal.Quotient.mk I a = 0 := by
    rw [← Good.kill R hRη _ h2, ← RingHom.comp_apply, hRη]
  have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 h3
  have e : x = (x - Δ.s j a) + Δ.s j a := by ring
  rw [e]
  exact Ideal.add_mem _ ha (Ideal.mem_map_of_mem _ haI)

theorem LeafStage_of : LeafStage := fun _ _ _ Δ c hc η hη =>
  ⟨stage_fin Δ c hc, stage_ideal Δ c hc η hη⟩

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

variable {A : Type} [CommRing A]

theorem inv_retr (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) :
    ∃ r : Localization.Away x →+* A ⧸ I, r.comp (algebraMap A (Localization.Away x)) = Ideal.Quotient.mk I := by
  have hu0 : IsUnit (Ideal.Quotient.mk I x) := by rw [hx]; exact isUnit_one
  exact ⟨IsLocalization.Away.lift (S := Localization.Away x) (g := Ideal.Quotient.mk I) x hu0,
    IsLocalization.Away.lift_comp (S := Localization.Away x) x hu0⟩

theorem inv_surj (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) (s : Localization.Away x) :
    ∃ a : A, s - algebraMap A (Localization.Away x) a ∈ I.map (algebraMap A (Localization.Away x)) := by
  obtain ⟨⟨a, ⟨u, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) s
  refine ⟨a, ?_⟩
  have h1 := IsLocalization.mk'_spec (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)
  have h2 : 1 - x ^ n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hx, one_pow, map_one, sub_self]
  rw [← h1]
  have h3 : IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) -
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (x ^ n) =
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (1 - x ^ n) := by
    rw [map_sub, map_one, mul_sub, mul_one]
  rw [h3]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ h2)

theorem inv_univ (I : Ideal A) (i : A) (hi : i ∈ I) : Univ (algebraMap A (Localization.Away (1 + i))) I := by
  intro B _ J hJ ψ hψ
  have hu : IsUnit (ψ (1 + i)) := by
    have hj : ψ i ∈ Ideal.jacobson ⊥ := by
      rw [Ideal.jacobson_bot]
      exact hJ.jac (hψ hi)
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    rw [mul_one, add_comm] at this
    rwa [map_add, map_one]
  refine ⟨IsLocalization.Away.lift (1 + i) hu, RingHom.ext fun a => IsLocalization.Away.lift_eq (1 + i) hu a, ?_⟩
  intro χ hχ
  apply IsLocalization.ringHom_ext (Submonoid.powers (1 + i))
  rw [hχ]
  exact RingHom.ext fun a => (IsLocalization.Away.lift_eq (1 + i) hu a).symm

theorem LeafInv_of : LeafInv := by
  intro A _ I i hi
  have hx : Ideal.Quotient.mk I (1 + i) = 1 := by
    rw [map_add (f := _), map_one, Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  refine ⟨Localization.Away (1 + i), inferInstance, algebraMap A (Localization.Away (1 + i)),
    ⟨?_, inv_retr I _ hx, inv_surj I _ hx, inv_univ I i hi⟩, IsLocalization.Away.algebraMap_isUnit (1 + i)⟩
  rw [RingHom.etale_algebraMap]
  exact Algebra.Etale.of_isLocalizationAway (1 + i)

end LateralTheory.CohomologicalPurity.Hz
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafColUniv_of : LeafColUniv := by
  intro A _ I Δ c hc η hη B _ J hJ ψ hψ
  have hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ := fun j => (Δ.good j).univ B J hJ ψ hψ
  choose χ hχ hχu using hu
  have hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j := fun {j k} e => by
    apply hχu j
    rw [RingHom.comp_assoc, Δ.nat e, hχ k]
  let cB : Cocone Δ.D := ⟨CommRingCat.of B, ⟨fun j => CommRingCat.ofHom (χ j), fun j k e => by
    apply CommRingCat.hom_ext
    simpa using hnat e⟩⟩
  let d := hc.desc cB
  have hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j := fun j => by
    have := hc.fac cB j
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  refine ⟨d.hom, ?_, fun χ' h' => ?_⟩
  · show d.hom.comp η = ψ
    rw [← hη j₀, ← RingHom.comp_assoc, hfac, hχ]
  · have h2 : ∀ j, χ'.comp (Δ.leg c j) = χ j := fun j => by
      apply hχu j
      rw [RingHom.comp_assoc, hη j, h']
    have : CommRingCat.ofHom χ' = d := hc.hom_ext fun j => by
      apply CommRingCat.hom_ext
      change χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)
      rw [h2, hfac]
    rw [← this]
    rfl

end LateralTheory.CohomologicalPurity.Hz
end
end
