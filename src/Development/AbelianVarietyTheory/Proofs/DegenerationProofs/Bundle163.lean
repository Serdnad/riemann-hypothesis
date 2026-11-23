module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorus
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle123
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
section
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F} (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A}

theorem Carries.eq {ν : NumOf D F N} {ν' : NumOf D' F N'} {x : N.A} {x' : N'.A} (h : Carries ν ν' φ x x') :
    lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _ = ν'.eA x' := by
  rw [← Category.assoc, h, lift_snd]

theorem exists_equiv (hφ : HomF φ) : ∃ f : N.A ≃* N'.A, ∀ x, Carries ν ν' φ x (f x) := by
  have hi : φ.inv ≫ fst _ _ = fst _ _ := by rw [Iso.inv_comp_eq, hφ.1]
  have c : ∀ x, Carries ν ν' φ x (ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) := fun x => by
    unfold Carries
    ext1
    · rw [Category.assoc, hφ.1, lift_fst, lift_fst]
    · rw [lift_snd, MulEquiv.apply_symm_apply, Category.assoc]
  let f : N.A →* N'.A := MonoidHom.mk' (fun x => ν'.eA.symm (lift (𝟙 _) (ν.eA x) ≫ φ.hom ≫ snd _ _)) fun x y => by
    rw [map_mul ν.eA, hφ.2, map_mul]
  refine ⟨MulEquiv.ofBijective f ⟨fun x y h => ?_, fun y => ?_⟩, c⟩
  · have e : lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν.eA y) ≫ φ.hom :=
      (c x).trans ((congrArg (fun z => lift (𝟙 _) (ν'.eA z)) h).trans (c y).symm)
    have := congrArg (· ≫ snd _ _) ((cancel_mono _).1 e)
    simp only [lift_snd] at this
    exact ν.eA.injective this
  · refine ⟨ν.eA.symm (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _), ν'.eA.symm_apply_eq.2 ?_⟩
    have e : lift (𝟙 _) (lift (𝟙 _) (ν'.eA y) ≫ φ.inv ≫ snd _ _) = lift (𝟙 _) (ν'.eA y) ≫ φ.inv := by
      ext1
      · rw [Category.assoc, hi, lift_fst, lift_fst]
      · rw [lift_snd, Category.assoc]
    rw [MulEquiv.apply_symm_apply, e, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

theorem wVal_ne (w : BunIso φ) {f : N.A → N'.A} {x : N.A} (h : Carries ν ν' φ x (f x)) : wVal ν ν' w f x ≠ 0 := by
  have z : Sp F := (default : PrimeSpectrum F)
  have e₁ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, lift_snd]
  have e₂ : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left =
      (ν'.eA (f x)).left := by
    rw [← Over.comp_left, h.eq]
  have m₁ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left) z ∈
      D.P.L.U (ν.J (ν.eA x).left) := by rw [e₁]; exact ν.good _ trivial
  have m₂ : ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) z ∈
      D'.P.L.U (ν'.J (ν'.eA (f x)).left) := by rw [e₂]; exact ν'.good _ trivial
  have hle : ⊤ ≤ (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ⁻¹ᵁ
      (LB.div (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)
        (D.P.L.pull (snd (TF (R := R) F) D.P.A).left)).U
        (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left) := by
    intro y _
    have : y = z := by
      letI := y.isPrime
      letI := z.isPrime
      exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
    subst y
    exact ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩
  unfold wVal valF
  rw [dite_eq_left hle]
  exact ((w.s _).isUnit.map _ |>.map _).ne_zero

theorem exists_iso (hG : GlobalFnsSt) (w : BunIso φ) (hφ : HomF φ) (hw : w.IsGen) (hne : ∃ x, N'.th x ≠ 0) :
    ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧ ∀ x, Carries ν ν' φ x (I.φ x) := by
  obtain ⟨f, hf⟩ := exists_equiv ν ν' hφ
  have h₁ := GlobalTheory.T.abelianPartIso_carries_cube_values hG R D D' F N N' ν ν' φ w f hφ hw hf
  have h₂ := GlobalTheory.T.abelianPartIso_carries_symmetry_values hG R D D' F N N' ν ν' φ w f hφ hw hf
  obtain ⟨c, h₃⟩ := GlobalTheory.T.exists_abelianPartIso_theta_section_scale R D D' F N N' ν ν' φ w f hφ hw hf
  have h₀ := fun x => wVal_ne ν ν' w (hf x)
  have hc : c ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, rfl⟩ := f.surjective x
    rintro rfl
    exact hx (by rw [h₃, zero_mul, zero_mul])
  have h1 := h₀ 1
  refine ⟨⟨f, fun x => Units.mk0 (wVal ν ν' w f x / wVal ν ν' w f 1) (div_ne_zero (h₀ x) h1), Units.ext (div_self h1),
    fun x y u => Units.ext ?_, fun x => Units.ext ?_, Units.mk0 (c * wVal ν ν' w f 1) (mul_ne_zero hc h1), fun x => ?_⟩,
    ⟨φ, w, wVal ν ν' w f, hφ.1, hw, hf, fun _ => rfl, fun x => div_mul_cancel₀ _ h1⟩, hf⟩
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₁ x y u
  · simp only [Units.val_mul, Units.val_mk0]
    field_simp
    linear_combination h₂ x
  · simp only [Units.val_mul, Units.val_mk0]
    rw [h₃]
    field_simp
end

theorem main : Laws → ThetaPtDeterminesSt → BrUthSt → UrCSt := by
  intro hL hQ hU R _ _ D D' e₁ b₁ e₂ b₂ C _ _ _ _ _ N N' ν ν' q q' n hn ho hnC hI hI' hT hT' mt hA hg e hB hTm
  have hn0 : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at hnC; exact zero_ne_one hnC
  obtain ⟨Q, Φ, hΦ⟩ := exists_isFib hL.polBaseChange D C
  obtain ⟨Q', Φ', hΦ'⟩ := exists_isFib hL.polBaseChange D' C
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_abelianFibre_iso_of_matched_torsion_theta hL hQ hU R D D' e₁ b₁ e₂ b₂ hg C N N' ν ν' Q Q' Φ Φ' hΦ hΦ' n hn ho hn0
  choose ρ hρ hρ' hρ'' using GlobalTheory.T.exists_torsion_map_of_theta_matching C N N' q q' n _ _ hn ho hnC hI hI' hT hT' mt hA e hTm
  have key : ∀ j, j₀ ≤ j → ∃ I : NumB.Iso N.toNumB N'.toNumB, GeoIso ν ν' I ∧
      ∀ b, b ^ (n ^ j) ^ 2 = 1 → I.φ b = ρ j b := fun j hj => by
    obtain ⟨σ, hσ, hs⟩ := H j hj _ _ mt.c₀_ne (hρ j)
    obtain ⟨φ, w, hφ, hw, hp⟩ := GlobalTheory.T.exists_product_iso_of_fibre_iso_field R D D' C Q Q' Φ Φ' hΦ hΦ' σ hσ
    obtain ⟨t, -, ht⟩ := hT'.good 1
    obtain ⟨I, hI, hc⟩ := exists_iso ν ν' hL.globalFns w hφ hw ⟨_, fun h => by
      rw [h, norm_zero] at ht; exact zero_ne_one ht⟩
    refine ⟨I, hI, fun b hb => ν'.eA.injective ?_⟩
    exact (hc b).eq.symm.trans (Carries.eq (hp _ _ fun x hx => hs x b hb hx))
  obtain ⟨I, hG, hI₀⟩ := key (j₀ + 1) (Nat.le_succ _)
  have om : ∀ j, Odd (n ^ j) := fun j => ho.pow
  refine ⟨I, fun i p p' hr h1 h1' => ?_, ?_, hG⟩
  · obtain ⟨I', -, hI₁⟩ := key (j₀ + 1 + i) (by omega)
    have ag : ∀ b, b ^ (n ^ (j₀ + 1)) ^ 2 = 1 → I'.φ b = I.φ b := fun b hb => by
      obtain ⟨p, p', hr, a, a', rfl⟩ := hρ'' _ b hb
      rw [hI₀ _ hb, ← hρ' _ _ le_rfl p p' hr a a', hI₁, ← hρ' _ _ (by omega) p p' hr a a']
      rw [pow_add, mul_pow, pow_mul, hb, one_pow]
    have eq : ∀ x, I'.φ x = I.φ x := fun x => by
      refine hT'.sep (j₀ + 1) (by omega) _ _
        ((I'.lam * I'.h x ^ (n ^ (j₀ + 1)) ^ 2 / (I.lam * I.h x ^ (n ^ (j₀ + 1)) ^ 2) : Cˣ) : C) (Units.ne_zero _)
        fun b' hb' => ?_
      obtain ⟨b, rfl⟩ := I.φ.surjective b'
      have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := I.φ.injective (by rw [map_pow, hb', map_one])
      rw [RecPeriods.uth_iso I _ (om _) b x hb, ← ag b hb, RecPeriods.uth_iso I' _ (om _) b x hb, ← _root_.mul_assoc,
        ← Units.val_mul, div_mul_cancel]
    have hb : p.1.2.b ^ n ^ i = 1 := by rw [N.QT_pow_b, h1, toAdd_one, N.c_zero]
    rw [← eq, hI₁, hρ' (j₀ + 1 + i) i (by omega) p p' hr h1 h1']
    rw [← pow_mul, show (j₀ + 1 + i) * 2 = i + (2 * j₀ + 2 + i) by ring, pow_add, pow_mul, hb, one_pow]
  · obtain ⟨t, ht, ht'⟩ := hT.good 1
    have dv : ∀ (j : ℕ) (x : N.A), ∃ y, y ^ n ^ j = x := fun j => by
      induction j with
      | zero => exact fun x => ⟨x, by rw [pow_zero, pow_one]⟩
      | succ j ih =>
        intro x
        obtain ⟨y, rfl⟩ := hT.div x
        obtain ⟨z, rfl⟩ := ih y
        exact ⟨z, by rw [pow_succ, pow_mul]⟩
    obtain ⟨b, rfl⟩ := dv (j₀ + 1) t
    have hb : b ^ (n ^ (j₀ + 1)) ^ 2 = 1 := by
      rw [sq, pow_mul, pow_succ' n j₀, pow_mul _ n, ← pow_succ', ht, one_pow]
    have a := RecPeriods.uth_iso I _ (om _) b 1 hb
    rw [map_one, hI₀ b hb, ((hρ _).2 b hb).2, I.h_one, one_pow, _root_.mul_one] at a
    have nz : N.uth (n ^ (j₀ + 1)) b 1 ≠ 0 := by
      refine mul_ne_zero (Units.ne_zero _) (mul_ne_zero (fun h => ?_) (Units.ne_zero _))
      rw [_root_.one_mul] at ht' h
      rw [h, norm_zero] at ht'
      exact zero_ne_one ht'
    exact (mul_right_cancel₀ nz a).symm

end GlobalTheory.Ex.AbPartIso
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.families_values_correspond : Laws → Laws2 → BrFamSt := by
  first | exact @GlobalTheory.Ex.brFam | exact GlobalTheory.Ex.brFam | (intros; apply GlobalTheory.Ex.brFam <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.DivSemi

theorem smooth_proj {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) : Smooth q.left := by
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem dim_eq_add {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) {g g' : ℕ}
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := smooth_proj h
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left] (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem isMonHom_id_pow {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (n : ℕ) :
    IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))

theorem exists_torus_abelian_quotient :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ p = y) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ IsAbelianScheme B ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  intro k _ _ p _ _ G _ hG hp
  obtain ⟨X, _, _, _, B, _, i, q, hQ, hmax⟩ := GlobalTheory.T.exists_torusQuotient_no_cocharacter k G hG
  have hsm := smooth_proj hQ
  have hQ' := hQ
  obtain ⟨hi, hq, hf, hs, ha, hk, hB⟩ := hQ'
  have hB' := hB
  obtain ⟨hc, h₁, h₂, h₃, h₄⟩ := hB'
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom h₁ h₄
  have hint : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hfin : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1} := by
    have e : ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ((𝟙 B) ^ p : B ⟶ B) = x ^ p := fun x => by
      rw [MonObj.comp_pow, Category.comp_id]
    have := GlobalTheory.SS.finite_ker_of_surjective_points k B hB ((𝟙 B) ^ p) (isMonHom_id_pow B p) fun y => by
      obtain ⟨y', rfl⟩ := exists_lift_point q y
      obtain ⟨x, rfl⟩ := hp y'
      exact ⟨x ≫ q, by rw [e, MonObj.pow_comp]⟩
    simpa only [e] using this
  have hpr : IsProper B.hom := by
    refine GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed k B h₂ inferInstance h₃ fun a ha => ?_
    by_contra hn
    rcases GlobalTheory.T.infinite_torsion_or_cocharacter_of_arc_at_infinity k p B hB a ha hn with h | ⟨f, hf, hf'⟩
    · exact not_finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1}
    · exact hf' (hmax f hf)
  refine ⟨X, _, ‹_›, ‹_›, B, _, i, q, hQ, ⟨hc, h₁, hpr, h₄⟩, fun g hg => ?_⟩
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨a, ha⟩ := exists_dim_of_preconnected B.hom x
  exact ⟨a, ha, dim_eq_add (default : PrimeSpectrum k) hQ hg ha⟩

end GlobalTheory.SS.DivSemi
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.nonempty_torusExtension_of_surjective_points' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  first | exact @GlobalTheory.SS.nonempty_torusExtension_of_surjective_points | exact GlobalTheory.SS.nonempty_torusExtension_of_surjective_points | (intros; apply GlobalTheory.SS.nonempty_torusExtension_of_surjective_points <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

theorem _root_.GlobalTheory.T.isMonHom_generic_fibre_kernel_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → IsMonHom i := by
  first | exact @GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | exact GlobalTheory.ZJ.KerSubgroup.isMonHom_generic | (intros; apply GlobalTheory.ZJ.KerSubgroup.isMonHom_generic <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AdaptedSep

theorem basis_separates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨_, h₂, h₃, h₄, h₅, h₆, h₇⟩
  obtain ⟨m, t, ht⟩ := CrdMove.immBy_lbPow hL.1.ample _ u.A k hk
  obtain ⟨s, hs⟩ := CrdMove.exists_transport u.A.isLB u.U.LG.isLB u.U.gen.hom.left u.U.gen.inv.left
    (congrArg (fun q => q.left) u.U.gen.inv_hom_id) (congrArg (fun q => q.left) u.U.gen.hom_inv_id) _ u.U.ext k t
  choose b hb using fun i => AdaptedSpan.exists_comb hL.1.globalFns u.U (by omega : 1 ≤ k) σ cls f h₂ h₃ h₄ h₅ h₆ h₇ (s i)
  have key : ∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (lbPow u.A.L k) t (a.left ≫ u.U.gen.hom.left)
      (fun i => ∑ j, algebraMap (FractionRing u.V) (PadicAlgCl p) (b i j) * w j) := fun a w h =>
    hs _ a.left _ (CrdMove.crd_comb (pullback.condition : pullback.fst u.G.hom (jK u.V) ≫ u.G.hom = _)
      (fun _ => (Category.comp_id _).symm) σ s b hb a.left _ (Over.w a) h)
  refine ⟨fun a w h hw => ?_, fun a a' w h h' => ?_, fun a ha => ?_⟩
  · have hm : (a.left ≫ u.U.gen.hom.left : Sp (PadicAlgCl p) ⟶ u.A.A.left) (IsLocalRing.closedPoint _) ∈
        ⨆ i ∈ Set.univ, nonzeroLocus (t i) := by rw [ht.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hu := (CrdCalc.crd_isUnit_iff i (key a w h)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    simp [hw] at hu
  · have e := ImmSep.eq_of_crd_eq _ _ _ _ _ t _ (DVR.linComb_isLB _ u.A.isLB _ _) ht _ _ _ _
      ((Over.w (a ≫ u.U.gen.hom)).trans (Over.w (a' ≫ u.U.gen.hom)).symm) (key a w h) (key a' w h')
    exact (cancel_mono u.U.gen.hom).1 (Over.OverMorphism.ext e)
  · have e : gPt p ≫ spMap u.j = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V :=
      (Spec.map_comp _ _).symm.trans (Eq.trans rfl (Spec.map_comp
        (CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)))
        (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))))
    exact ⟨Over.homMk (pullback.lift a (jFK (R := u.V) (PadicAlgCl p)) (ha.trans e)) (pullback.lift_snd _ _ _),
      pullback.lift_fst _ _ _⟩

end GlobalTheory.ZH.AdaptedSep
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_theta_pullback_nonzero_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  first | exact @GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre | exact GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre | (intros; apply GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.card_torsion_abelianVariety_le_const_mul_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ a, SmoothOfRelativeDimension a B.hom → ∃ C : ℕ, ∀ n : ℕ, (n : k) ≠ 0 → Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} ≤ C * n ^ (2 * a) := by
  first | exact @GlobalTheory.SS.card_torsion_le | exact GlobalTheory.SS.card_torsion_le | (intros; apply GlobalTheory.SS.card_torsion_le <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait.LevelFour

theorem exists_image {C : Type} [Field C] {N N' : NumD C} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ q : N'.QT k, q.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 q.1.2 := by
  obtain ⟨h₁, h₂, h₃, -⟩ := NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)
  obtain ⟨g, hg, -⟩ := h₁ p.1.2
  have hp : ∀ n : ℕ, J.Rel (p.1.2 ^ n) (g ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact J.rel_one
    | succ n ih => rw [pow_succ, pow_succ]; exact h₂ _ _ _ _ ih hg
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, hg⟩
  have a := hp k
  rw [N.mem_QT.1 p.2] at a
  exact (h₁ _).unique a (h₃ _)

theorem ev_iso {C : Type} [NormedField C] {N N' : NumD C} (J : NumD.Iso N N') {m : ℕ} (hm : Odd m)
    {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h₁ : p'.1.1.toAdd = J.e p.1.1.toAdd) (h₂ : J.Rel p.1.2 p'.1.2)
    {g : N.Gt} {g' : N'.Gt} (hg : J.Rel g g') :
    N'.ev m p' g' = (J.lam * J.h g.b ^ (m ^ 2) : Cˣ) * N.ev m p g := by
  have H := (NumD.hom_transport C C (RingHom.id C) N N' (TateInh.homOfIso J)).2.2.2.2 m hm p p' h₁ h₂
  rw [NumD.ev, NumD.ev, ← J.e.toEquiv.tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun χ => (H χ).2 g g' hg

theorem labels_of_four_le : GlobalTheory.UT.LL → EVSt → BrGtSt → AllS fun {_} _ _ _ {_} {_} {_} {_} {_} _ {_} {_} _ _ {_} _ {_} _ _ A u r {o} M _ {_} ν' J => M.P.TorsionIso → Realises o A.arc A.be u r → ∀ n : ℕ, Odd n → 3 ≤ n → Labels A u r M ν' J (n ^ 2) → ∀ k, 4 ≤ k → Labels A u r M ν' J k := by
  intro hL hE hB E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J hr _ hT hR n hn h3 hl k hk
    x p q' p' z hp e₁ e₂ hq hz
  have hn2 : 0 < n ^ 2 := pow_pos hn.pos 2
  have B := hB M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  choose pt hpt using fun i : D.La => (existsUnique_twRel A.be u (r (n ^ 2)) (hr.pow hn2) (A.q (n ^ 2) i)).exists
  choose qt hq₁ hq₂ using fun i => exists_image J (pt i)
  choose pp hpp using fun i => (B.2.2.2.2 (n ^ 2)).2.1 (qt i)
  have hA : ∀ i, M.P.ToA C (n ^ 2) (pp i) (e (o.I.ev (n ^ 2) i)) := fun i =>
    hl i (pt i) (qt i) (pp i) _ (hpt i) (hq₁ i) (hq₂ i) (hpp i) (he _)
  obtain ⟨F, hF, -⟩ := hT C k (by omega)
  obtain ⟨y, hy⟩ := e.surjective (F p')
  have Q := hE M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext N' ν' n hn D.La pp qt _ hA hpp
    k hk p' q' (F p') ((hF _ _).2 rfl) hq
  let τ : (baseOver (Sp C)).left ⟶ (TFK (R := M.W) C).left := 𝟙 (Sp C)
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp C)))
  have hτ : τ ≫ (TFK (R := M.W) C).hom = (baseOver (Sp C)).hom ≫ jFK (R := M.W) C := rfl
  have ht : ∀ i, o.I.ev (n ^ 2) i ^ (n ^ 2) = 1 := fun i => (o.I.onto _ hn2 _).2 ⟨i, rfl⟩
  have Q₁ : IsCoordPt o.P n (T := baseOver (Sp C)) (o.I.ev (n ^ 2)) y fun i => fnOf (N'.ev n (qt i) q'.1.2) :=
    FullExtend.isCoordPt_move τ M.cart M.lb τ (𝟙 _) (Category.comp_id _) hτ (fun th h s => by
      obtain ⟨c, hc⟩ := h s
      have e := VVRank.pullM_id M.P.A.A M.P.A.isLB 1 (SecM.ofSec M.P.A.A th)
      exact ⟨c, fun j => (hc j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩)
      (fun i => (Category.id_comp _).trans (he _)) ht (z := y)
      ((Category.id_comp _).trans ((congrArg (fun w => w.left) hy).symm.trans (he _))) Q
  have Q₂ := ((hR.2.2.2 n hn pt hpt).2.2 k (by omega) x p hp).2
  obtain ⟨-, s₂, -, s₄⟩ := CoordSep.coord_exists_unique_separate hL.1 C (Sp C) o.P (𝟙 _) n hn
    (Nat.cast_ne_zero.2 hn.pos.ne') D.La (o.I.ev (n ^ 2)) ht
  have Q₃ := (s₂ _ _ (fun i => N'.ev n (qt i) q'.1.2) Q₂).2
    ⟨J.lam * J.h p.1.2.b ^ (n ^ 2), funext fun i => ev_iso J hn (hq₁ i) (hq₂ i) e₂⟩
  obtain rfl := (s₄ h3 (fun w hw => (o.I.onto _ hn2 w).1 hw) _ _ _ Q₃ Q₁).1
  exact (hF _ _).2 ((Over.OverMorphism.ext (hz.trans (he _).symm)).trans hy)

end GlobalTheory.Ex.Trait.LevelFour
end
