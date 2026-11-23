module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

section

open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) :
    R ⧸ lev ϖ k →+* R ⧸ lev ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((Ideal.Quotient.mk (lev ϖ k)).comp σ) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

@[simp] theorem barσ_mk {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (a : R) :
    barσ σ ϖ h k (Ideal.Quotient.mk (lev ϖ k) a) = Ideal.Quotient.mk (lev ϖ k) (σ a) := rfl

structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)

variable {E : Type} [CommRing E] {τ : E →+* E}

structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

variable {V : Type} [AddCommGroup V] [Module E V]

namespace HermSp

variable (B : HermSp E τ V)

theorem zero_left (w : V) : B.h 0 w = 0 := by
  have h0 := B.smul_left 0 0 w
  rwa [zero_smul, zero_mul] at h0

theorem add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add (f := _), ← B.symm, ← B.symm]

theorem smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]

theorem self_fixed (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by
  exact (B.symm v v).symm

def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [B.smul_left, hx, mul_zero]

noncomputable def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)

theorem coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hu : ((hw.unit⁻¹ : Eˣ) : E) * B.h w w = 1 := by
    have h1 := hw.unit.inv_mul
    simpa using h1
  have hc : B.coef hw z * B.h w w = B.h z w := by
    unfold coef
    rw [mul_assoc, hu, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by
    rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e

noncomputable def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := by simp [B.add_left]
  smul_left a v x := by simp [B.smul_left]
  symm v x := B.symm _ _
  nondeg := by
    intro v hv
    apply Subtype.ext
    apply B.nondeg
    intro z
    have h1 := hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩
    have hz : z = (z - B.coef hw z • w) + B.coef hw z • w := by abel
    have h0 : B.h (v : V) w = 0 := v.2
    rw [hz, B.add_right, B.smul_right, h0, mul_zero, add_zero]
    exact h1

@[simp] theorem perpForm_h {w : V} (hw : IsUnit (B.h w w)) (a b : B.perp w) :
    (B.perpForm hw).h a b = B.h a b := rfl

noncomputable def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := by
    rintro ⟨a, v⟩
    have h0 : B.h (v : V) w = 0 := v.2
    have hc : B.coef hw (a • w + (v : V)) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, h0, add_zero, mul_assoc]
      have : B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 := by
        have := hw.unit.mul_inv
        simpa using this
      rw [this, mul_one]
    ext
    · exact hc
    · simp [hc]
  right_inv := by
    intro z
    simp

theorem perpEquiv_apply {w : V} (hw : IsUnit (B.h w w)) (p : E × B.perp w) :
    B.perpEquiv hw p = p.1 • w + (p.2 : V) := rfl

theorem norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by
  have hwv : B.h w v = 0 := by rw [B.symm v w, hv, map_zero]
  simp only [B.add_left, B.smul_left, B.add_right, B.smul_right, hv, hwv, mul_zero, add_zero]
  ring

end HermSp

def HermSp.ofMatrix (hτ : ∀ a, τ (τ a) = a) {m : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) : HermSp E τ (Fin m → E) where
  h v w := dotProduct (fun i => τ (w i)) (S.mulVec v)
  add_left u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  smul_left a v w := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  symm v w := by
    have hij : ∀ i j, τ (S j i) = S i j := fun i j => by
      have := congrFun (congrFun hS i) j
      simpa [cT] using this

    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, hij]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg v hv := by
    have h0 : S.mulVec v = 0 := by
      funext i
      have := hv (Pi.single i 1)
      simpa [dotProduct, Pi.single_apply] using this
    have := congrArg (S⁻¹).mulVec h0
    have hu : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hd
    simpa [Matrix.mulVec_mulVec, hu] using this

theorem gram_apply (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by
  show (cT τ x * S * x) i j = dotProduct (fun a => τ (x a i)) (S.mulVec (fun a => x a j))
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CompanionTheory.UnrDens
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open CategoryTheory.Limits

namespace GlobalTheory.CompanionTheory.SecAdd

variable {S : Type} [CommRing S]

theorem away_self_eq_one {e : S} (he : IsIdempotentElem e) :
    algebraMap S (Localization.Away e) e = 1 := by
  have hu : IsUnit (algebraMap S (Localization.Away e) e) := IsLocalization.Away.algebraMap_isUnit e
  have h : algebraMap S (Localization.Away e) e * algebraMap S (Localization.Away e) e
      = algebraMap S (Localization.Away e) e * 1 := by
    rw [← map_mul, he.eq, mul_one]
  exact hu.mul_left_cancel h

theorem away_orth_eq_zero {e x : S} (he : IsIdempotentElem e) (h : e * x = 0) :
    algebraMap S (Localization.Away e) x = 0 := by
  have := congrArg (algebraMap S (Localization.Away e)) h
  rwa [map_mul, away_self_eq_one he, one_mul, map_zero] at this

theorem away_surj {e : S} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap S (Localization.Away e)) := by
  intro b
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers e) b
  obtain ⟨n, hn⟩ := s.2
  refine ⟨x, ?_⟩
  have : algebraMap S (Localization.Away e) (s : S) = 1 := by
    rw [← hn, map_pow, away_self_eq_one he, one_pow]
  simp only [this, mul_one] at hx
  exact hx.symm

theorem away_ker {e x : S} (he : IsIdempotentElem e)
    (h : algebraMap S (Localization.Away e) x = 0) : e * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) _ x).1 h
  rcases n with _ | n
  · simp at hc
    simp [hc]
  · have : e ^ (n + 1) = e := he.pow_succ_eq n
    simpa [this] using hc

theorem isIdempotentElem_add {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) : IsIdempotentElem (e + e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  unfold IsIdempotentElem
  rw [add_mul, mul_add, mul_add, h, h', he.eq, he'.eq, add_zero, zero_add]

theorem isLocalization_prod {e e' : S} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : e * e' = 0) :
    IsLocalization.Away (e + e') (Localization.Away e × Localization.Away e') := by
  have h' : e' * e = 0 := by rw [mul_comm, h]
  have key : ∀ z : S, algebraMap S (Localization.Away e × Localization.Away e') z = 0 ↔
      (e + e') * z = 0 := by
    intro z
    constructor
    · intro hz
      have h1 : algebraMap S (Localization.Away e) z = 0 := congrArg Prod.fst hz
      have h2 : algebraMap S (Localization.Away e') z = 0 := congrArg Prod.snd hz
      rw [add_mul, away_ker he h1, away_ker he' h2, add_zero]
    · intro hz
      have h1 : e * z = 0 := by
        have := congrArg (e * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he.eq, h, add_zero]
      have h2 : e' * z = 0 := by
        have := congrArg (e' * ·) hz
        simp only [mul_zero] at this
        rw [← this, ← mul_assoc, mul_add, he'.eq, h', zero_add]
      exact Prod.ext (away_orth_eq_zero he h1) (away_orth_eq_zero he' h2)
  refine IsLocalization.away_of_isIdempotentElem_of_mul (isIdempotentElem_add he he' h) ?_ ?_
  · intro x y
    rw [← sub_eq_zero, ← map_sub, key, mul_sub, sub_eq_zero]
  · rintro ⟨b, c⟩
    obtain ⟨x, rfl⟩ := away_surj he b
    obtain ⟨y, rfl⟩ := away_surj he' c
    refine ⟨e * x + e' * y, Prod.ext ?_ ?_⟩
    · change algebraMap S (Localization.Away e) (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e) e' = 0 := away_orth_eq_zero he h
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he, this, one_mul, zero_mul, add_zero]
    · change algebraMap S (Localization.Away e') (e * x + e' * y) = _
      have : algebraMap S (Localization.Away e') e = 0 := away_orth_eq_zero he' h'
      rw [map_add (f := _), map_mul, map_mul, away_self_eq_one he', this, one_mul, zero_mul, zero_add]

theorem secOn_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' →
    e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  intro S _ Y f e e' he he' h ⟨s, hs⟩ ⟨s', hs'⟩
  haveI := isLocalization_prod he he' h
  let B := Localization.Away e
  let C := Localization.Away e'
  let A := Localization.Away (e + e')
  let φ : (B × C) ≃ₐ[S] A :=
    IsLocalization.algEquiv (Submonoid.powers (e + e')) (B × C) A
  let t : Spec (CommRingCat.of (B × C)) ⟶ Y := inv (coprodSpec B C) ≫ coprod.desc s s'
  have ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B × C))) := by
    rw [← cancel_epi (coprodSpec B C)]
    simp only [t, Category.assoc, IsIso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, hs, coprodSpec_inl_assoc, ← Spec.map_comp]
      rfl
    · rw [coprod.inr_desc_assoc, hs', coprodSpec_inr_assoc, ← Spec.map_comp]
      rfl
  refine ⟨Spec.map (CommRingCat.ofHom (φ : B × C →+* A)) ≫ t, ?_⟩
  rw [Category.assoc, ht, ← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

end GlobalTheory.CompanionTheory.SecAdd
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.etale_surjective_local_section : ∀ {S : Type} [CommRing S],
    Aic (S := S) → Loc (S := S) →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨B, i, hi, z, hz⟩ := Y.exists_Spec_apply_eq y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S B := φ.hom.toAlgebra
  have : Algebra.Etale S B := RingHom.etale_algebraMap.1 hφe
  let Q : Ideal B := z.asIdeal
  have hQ : Q.IsPrime := z.2
  have hQm : Q.comap (algebraMap S B) = m := by
    have hx : (Spec.map φ) z = x := by rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal hx
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  let q := Q.map (algebraMap B Bg)
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hq : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : q.comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hqm : q.comap (algebraMap S Bg) = m := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap, hQm]
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
  have hroot_of_mem (F : Polynomial S) (hF : F.Monic) (hmem : Polynomial.aeval P.x F ∈ q) :
      ∃ b : S, F.IsRoot b ∧ P.x - algebraMap S Bg b ∈ q := by
    have : Nontrivial S := nontrivial_of_ne 0 1 fun h =>
      hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))
    induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
    | ind n ih =>
      by_cases hn : n = 0
      · have h1 := Polynomial.eq_one_of_monic_natDegree_zero hF (hd.trans hn)
        rw [h1, map_one] at hmem
        exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hmem)).elim
      obtain ⟨b, hb⟩ := hA F hF (by omega)
      let G := F /ₘ (Polynomial.X - Polynomial.C b)
      have hFG : (Polynomial.X - Polynomial.C b) * G = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.2 hb
      have hG : G.Monic := (Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C b))
        (hFG.symm ▸ hF)
      have hdeg := (Polynomial.monic_X_sub_C b).natDegree_mul hG
      rw [hFG, Polynomial.natDegree_X_sub_C, hd] at hdeg
      rw [← hFG, map_mul] at hmem
      rcases hq.mem_or_mem hmem with hbq | hGq
      · exact ⟨b, hb, by simpa using hbq⟩
      · obtain ⟨c, hc, hcq⟩ := ih G.natDegree (by omega) G hG hGq rfl
        exact ⟨c, by rw [← hFG, Polynomial.IsRoot, Polynomial.eval_mul, hc, mul_zero], hcq⟩
  obtain ⟨b, hb, hbq⟩ := hroot_of_mem P.f P.monic_f (P.hasMap.1.symm ▸ q.zero_mem)
  let c : S := Polynomial.eval b P.g
  have hcm : c ∉ m := by
    rw [← hqm]
    intro hcq
    have hdvd : P.x - algebraMap S Bg b ∣ Polynomial.aeval P.x P.g - algebraMap S Bg c := by
      have h := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    have hgq : Polynomial.aeval P.x P.g ∈ q := by
      simpa using q.add_mem (Ideal.mem_of_dvd q hdvd hbq) (show algebraMap S Bg c ∈ q from hcq)
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hgq P.hasMap.2)
  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ m := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ m := by
    intro hem
    have h1 : (1 : S) ∈ m := by simpa using m.add_mem hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have hmul : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [hmul] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hb.eq_zero, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  let ψ := ((P.P.lift _ hmap).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom S B Bg)
  refine ⟨e, he, hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DivPow

theorem exists_gamma {S : Type} [CommRing S] (I : Ideal S) (z : S)
    (h : ∀ k : ℕ, k ≠ 0 → ∃ y ∈ I, (k.factorial : S) * y = z ^ k) :
    ∃ γ : ℕ → S, (∀ i, i ≠ 0 → γ i ∈ I) ∧ ∀ i, (i.factorial : S) * γ i = z ^ i := by
  classical
  refine ⟨fun i => if hi : i = 0 then 1 else (h i hi).choose, ?_, ?_⟩
  · intro i hi
    simpa [hi] using (h i hi).choose_spec.1
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp
    · simpa [hi] using (h i hi).choose_spec.2

theorem pdI_span : ∀ {S : Type} [CommRing S], TF (S := S) → ∀ s : Set S,
    (∀ x ∈ s, ∀ k : ℕ, k ≠ 0 → ∃ y ∈ Ideal.span s, (k.factorial : S) * y = x ^ k) →
    PdI (Ideal.span s) := by
  intro S _ _ s h x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    intro k hk
    exact ⟨0, Ideal.zero_mem _, by simp [zero_pow hk]⟩
  | smul a x _ ih =>
    intro k hk
    obtain ⟨y, hy, e⟩ := ih k hk
    refine ⟨a ^ k * y, Ideal.mul_mem_left _ _ hy, ?_⟩
    rw [smul_eq_mul, mul_pow, ← e]
    ring
  | add x x' _ _ ih ih' =>
    intro k hk
    obtain ⟨γ, hγ, e⟩ := exists_gamma _ x ih
    obtain ⟨γ', hγ', e'⟩ := exists_gamma _ x' ih'
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, γ p.1 * γ' p.2, ?_, ?_⟩
    · refine Ideal.sum_mem _ ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := by
          rintro rfl
          exact hk (by omega)
        exact Ideal.mul_mem_left _ _ (hγ' j hj)
      · exact Ideal.mul_mem_right _ _ (hγ i hi)
    · rw [Finset.mul_sum, (Commute.all x x').add_pow']
      refine Finset.sum_congr rfl ?_
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      subst hij
      rw [← e i, ← e' j, nsmul_eq_mul, Nat.choose_symm_add, ← Nat.add_choose_mul_factorial_mul_factorial i j]
      push_cast
      ring

end GlobalTheory.CompanionTheory.DivPow
end
