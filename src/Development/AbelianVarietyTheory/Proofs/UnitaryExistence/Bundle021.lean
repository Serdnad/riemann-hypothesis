module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.RiemannForm

theorem eq_of_im {g : ℕ} (h τ Hm A B : Matrix (Fin g) (Fin g) ℂ) (hA : h * A = 1) (hB : h * B = τ)
    (h1 : ∀ a b, ((Aᵀ * Hm * A.map (starRingEnd ℂ)) a b).im = 0)
    (h2 : ∀ a b, ((Aᵀ * Hm * B.map (starRingEnd ℂ)) a b).im = -(1 : Matrix (Fin g) (Fin g) ℝ) a b) :
    Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧
      Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  have hA' : A * h = 1 := mul_eq_one_comm.mp hA
  have hB' : B = A * τ := by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM
  have hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [hB', Matrix.map_mul, hM]; simp only [Matrix.mul_assoc]
  have hMY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext a b
    have := h2 a b
    rw [hMB, Matrix.mul_apply, Complex.im_sum] at this
    rw [Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [h1 a c]
  have hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re := Matrix.inv_eq_left_inv hMY
  have hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M := by
    ext a b
    apply Complex.ext <;> simp [h1 a b]
  have hH : Hm = hᵀ * M * h.map (starRingEnd ℂ) := by
    have e1 : hᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]
    have e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hA']; simp
    calc Hm = (hᵀ * Aᵀ) * Hm * (A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ)) := by
          rw [e1, e2]; simp
      _ = _ := by rw [hM]; simp only [Matrix.mul_assoc]
  refine ⟨by rw [hinv, hMre]; exact hH, ?_⟩
  have hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1 := by
    have e := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_one] at e
    have e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ) := by
      conv_lhs => rw [← hMre]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [e']; exact_mod_cast e
  have hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det :=
    (RingHom.map_det (starRingEnd ℂ) h).symm
  rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  have := Complex.mul_conj' h.det
  push_cast
  linear_combination (h.det * starRingEnd ℂ h.det) * hd + this

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → Fin g → ℂ) (a b : Fin g) :
    ((Matrix.of u)ᵀᵀ * Hm * ((Matrix.of v)ᵀ).map (starRingEnd ℂ)) a b = hermForm Hm (u a) (v b) := by
  rw [Matrix.mul_assoc]
  rfl

theorem herm_eq_of_normalised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (P : D.La →+ (Fin g → ℂ)) (h τ Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) → IsPeriod D ty P → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → τ ∈ SiegelH (Fin g) → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧ Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  intro E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH
  refine eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ
    (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_
  · ext i k
    have := congrFun (hn k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  · ext i k
    have := congrFun (hn k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd]
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all [eq_comm]

end GlobalTheory.RiemannForm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  haveI : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem natCast_ne_zero_of_isUnit_of_fieldPoint {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero

theorem finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by
  intro hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t
  suffices H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga //
      x ≫ io ≫ fst G G' = 1} by
    have e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
    rwa [e] at H
  haveI := hG'.comm
  haveI := hG'.smooth
  haveI := hG'.quasiCompact
  have h := isGrpPullback_pullback G' t
  let T : Over S := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)
  let ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G') := pushHom h _
  have hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t := fun y => rfl
  have hinj : Function.Injective ρ := fun y z hyz => by
    ext1
    refine pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)
    rw [← hρ, ← hρ, hyz]
  have hsurj : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  let s : G' ⟶ G ⊗ G' := lift 1 (𝟙 G')
  have hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ G') →* (T ⟶ G ⊗ G') := MonoidHom.mk' (fun y => y ≫ s) fun y z => by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
    · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G') :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).1 hxy
  let C := κ.range.comap (σ.comp ρ)
  have hC : Finite C := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t)))
      (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp
      (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C
      ((pullback.fst G'.hom t ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (pullback.fst G'.hom t ≫ s.left).continuous) (fun y => ⟨?_, fun hy => ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left :=
        (congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        have e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left := Category.assoc _ _ _
        rw [e, Scheme.Hom.comp_apply]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htors T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G G') hx).trans (hs₁ _)
      refine hinj ?_
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using hsurj
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G'))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from
    congrArg Subtype.val hxy]

end GlobalTheory
end
