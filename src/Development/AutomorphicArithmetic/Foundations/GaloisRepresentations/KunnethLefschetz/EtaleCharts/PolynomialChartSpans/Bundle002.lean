module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AppLEFromOfGlobalSectionsChartHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BCoord
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SegreGlue
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

private theorem exists_closed_prod {R : Type} [CommRing R] {X Y : Scheme.{0}} (N M : ℕ)
    (i : X ⟶ projectiveSpace R N) (j : Y ⟶ projectiveSpace R M)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ h : pullback (i ≫ toSpecBase R N) (j ≫ toSpecBase R M) ⟶
        projectiveSpace R (N * M + N + M),
      IsClosedImmersion h ∧
        h ≫ toSpecBase R (N * M + N + M) =
          pullback.fst (i ≫ toSpecBase R N) (j ≫ toSpecBase R M) ≫ i ≫ toSpecBase R N := by
  haveI : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{0}) :=
    ⟨fun f g hf hg => by
      haveI := hf
      haveI := hg
      exact IsClosedImmersion.comp f g⟩
  have hmap : IsClosedImmersion (pullback.map (i ≫ toSpecBase R N) (j ≫ toSpecBase R M)
      (toSpecBase R N) (toSpecBase R M) i j (𝟙 _)
      ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullbackMap (P := (@IsClosedImmersion : MorphismProperty Scheme.{0}))
      inferInstance inferInstance rfl rfl
  refine ⟨pullback.map (i ≫ toSpecBase R N) (j ≫ toSpecBase R M)
      (toSpecBase R N) (toSpecBase R M) i j (𝟙 _)
      ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl) ≫ segre R N M,
    inferInstance, ?_⟩
  rw [Category.assoc, segre_toSpecBase, pullback.lift_fst_assoc, Category.assoc]

theorem UpperTheory.Gal.KunnethLefschetz.G.projProd :
    UpperTheory.Gal.KunnethLefschetz.G.ProjProd := by
  intro R _ X Y p q hp
  obtain ⟨N, i, hi, rfl⟩ := hp
  have hprop : IsProper (PSpace.str R N) :=
    inferInstanceAs (IsProper (toSpecBase R N))
  refine ⟨?_, fun j hj => ⟨N, j ≫ i, inferInstance, by simp⟩, inferInstance⟩
  rintro ⟨M, j, hj, rfl⟩
  obtain ⟨h, hc, he⟩ := exists_closed_prod (R := R) N M i j
  exact ⟨_, h, hc, he⟩
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let v : PEmpty.{1} → MvPolynomial (Fin D) A := PEmpty.elim
  let P0 := Algebra.PreSubmersivePresentation.naive (R := A) (v := v) (σ := Fin D)
    (ι := PEmpty.{1}) PEmpty.elim (fun a => a.elim)
  let P1 : Algebra.SubmersivePresentation A _ (Fin D) PEmpty.{1} :=
    { toPreSubmersivePresentation := P0
      jacobian_isUnit := by
        classical
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have hv : Ideal.span (Set.range v) = ⊥ := by simp [v]
  let e : (MvPolynomial (Fin D) A ⧸ Ideal.span (Set.range v)) ≃ₐ[A] MvPolynomial (Fin D) A :=
    (Ideal.quotientEquivAlgOfEq A hv).trans (AlgEquiv.quotientBot A _)
  exact ⟨⟨Fin D, PEmpty.{1}, inferInstance, inferInstance, P1.ofAlgEquiv e,
    by simp [Algebra.Presentation.dimension]⟩⟩

private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  have H := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have hr : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, H.cancel_left_isIso,
      CommRingCat.hom_comp, H.cancel_right_isIso]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h
  haveI : SmoothOfRelativeDimension 0 U.ι := by
    rw [← Etale.iff_smoothOfRelativeDimension_zero]
    infer_instance
  rw [← Scheme.Hom.resLE_comp_ι f e]
  simpa using smoothOfRelativeDimension_comp n 0 (f.resLE U V e) U.ι

private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose O hxO hO using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O
    (top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

theorem blSmooth : BlowUpSmooth := by
  intro R _ _ Z W D _ _ π hπ
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : Smooth (Over.hom Z) := SmoothOfRelativeDimension.smooth (n := D) (f := Over.hom Z)
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  obtain ⟨-, -, hoff⟩ := blOff R π hπ
  have hp1 : SmoothOfRelativeDimension D (Over.Hom.left (p1 Z)) := by
    change SmoothOfRelativeDimension D (pullback.fst (Over.hom Z) (Over.hom Z))
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have h1 : SmoothOfRelativeDimension D (Over.Hom.left (π ≫ p1 Z)) := by
    apply ofPts
    intro w
    by_cases hw : Over.Hom.left π w ∈ Set.range (Over.Hom.left (dg Z))
    · obtain ⟨z, hz⟩ := hw
      obtain ⟨U, u, hzU, hc⟩ := coordEx R Z D z
      obtain ⟨c, -, -, hcN⟩ := (dChartEx R Z D).1 U u hc z hzU
      obtain ⟨b⟩ := blChart R π hπ D c
      have hwN : w ∈ Over.Hom.left π ⁻¹ᵁ c.N := by
        show Over.Hom.left π w ∈ c.N
        rw [← hz]
        exact hcN
      rw [← b.cov] at hwN
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hwN
      refine ⟨b.V j, hj, chart _ D c.coord.1 (b.aff j) (fun x hx => c.h1 (b.le j hx)) ?_⟩
      change RingHom.IsStandardSmoothOfRelativeDimension D
        (Scheme.Hom.appLE (Over.Hom.left π ≫ Over.Hom.left (p1 Z)) c.U (b.V j) _).hom
      rw [← Scheme.Hom.appLE_comp_appLE _ _ c.U c.N (b.V j) c.h1 (b.le j), CommRingCat.hom_comp]
      have hg := RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp (bCoord R π D c b j)
      have hcomp := hg.comp (stdC _ D)
      rw [MvPolynomial.eval₂Hom_comp_C, zero_add] at hcomp
      exact hcomp
    · haveI : IsClosedImmersion (Over.Hom.left (dg Z)) := by
        change IsClosedImmersion (pullback.diagonal (Over.hom Z))
        infer_instance
      let O0 : (Over.left (XX Z)).Opens :=
        ⟨(Set.range (Over.Hom.left (dg Z)))ᶜ,
          (Over.Hom.left (dg Z)).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨hiso, -⟩ := hoff O0 rfl
      refine ⟨Over.Hom.left π ⁻¹ᵁ O0, hw, ?_⟩
      change SmoothOfRelativeDimension D
        ((Over.Hom.left π ⁻¹ᵁ O0).ι ≫ Over.Hom.left π ≫ Over.Hom.left (p1 Z))
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hp1 _) _
  refine ⟨h1, ?_⟩
  rw [← Over.w (π ≫ p1 Z)]
  exact smoothOfRelativeDimension_comp D D _ _

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh (inter inter_le inter_le_comp mem_inter_iff)

namespace UpperTheory.Gal.KunnethLefschetz.G

section
variable {Y : Scheme.{0}}

private abbrev rs {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) := (Y.presheaf.map (homOfLE h).op).hom

private theorem rs_rs {U V T : Y.Opens} (h : V ≤ U) (h' : T ≤ V) (x : Γ(Y, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by
  change ((Y.presheaf.map (homOfLE h).op ≫ Y.presheaf.map (homOfLE h').op)).hom x = _
  rw [← Functor.map_comp]
  rfl

private theorem nzd_rs {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    {s : Γ(Y, U)} (hs : s ∈ nonZeroDivisors Γ(Y, U)) : rs h s ∈ nonZeroDivisors Γ(Y, V) := by
  have hf : (Scheme.Hom.appLE (𝟙 Y) U V h).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) (Q := RingHom.Flat) (𝟙 Y) inferInstance ⟨U, hU⟩ ⟨V, hV⟩ h
  have e : (Scheme.Hom.appLE (𝟙 Y) U V h).hom = rs h := by
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  rw [e] at hf
  letI : Algebra Γ(Y, U) Γ(Y, V) := (rs h).toAlgebra
  haveI : Module.Flat Γ(Y, U) Γ(Y, V) := hf
  have hr : IsSMulRegular Γ(Y, U) s := fun a b e => (mul_cancel_left_mem_nonZeroDivisors hs).1 e
  have hr' := IsSMulRegular.of_flat (S := Γ(Y, V)) hr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hr'
  change rs h s * x = rs h s * 0
  rw [mul_zero, mul_comm]
  exact hx

private theorem exists_unit (J : Y.IdealSheafData) {U₁ U₂ T : Y.Opens}
    (a₁ : IsAffineOpen U₁) (a₂ : IsAffineOpen U₂) (aT : IsAffineOpen T) (h₁ : T ≤ U₁) (h₂ : T ≤ U₂)
    {s₁ : Γ(Y, U₁)} {s₂ : Γ(Y, U₂)} (e₁ : J.ideal ⟨U₁, a₁⟩ = Ideal.span {s₁})
    (e₂ : J.ideal ⟨U₂, a₂⟩ = Ideal.span {s₂})
    (n₂ : s₂ ∈ nonZeroDivisors Γ(Y, U₂)) :
    ∃ g : Γ(Y, T)ˣ, rs h₁ s₁ = g.val * rs h₂ s₂ := by
  have key : ∀ {U : Y.Opens} (a : IsAffineOpen U) (h : T ≤ U) {s : Γ(Y, U)},
      J.ideal ⟨U, a⟩ = Ideal.span {s} → J.ideal ⟨T, aT⟩ = Ideal.span {rs h s} := by
    intro U a h s e
    have := J.map_ideal (U := ⟨T, aT⟩) (V := ⟨U, a⟩) h
    rw [e, Ideal.map_span, Set.image_singleton] at this
    exact this.symm
  have k₁ := key a₁ h₁ e₁
  have k₂ := key a₂ h₂ e₂
  have m₁ : rs h₁ s₁ ∈ Ideal.span {rs h₂ s₂} := by
    rw [← k₂, k₁]; exact Ideal.mem_span_singleton_self _
  have m₂ : rs h₂ s₂ ∈ Ideal.span {rs h₁ s₁} := by
    rw [← k₁, k₂]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 m₁
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 m₂
  have n := nzd_rs a₂ aT h₂ n₂
  have hab : a * b = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors n).1 ?_
    calc rs h₂ s₂ * (a * b) = b * (a * rs h₂ s₂) := by ring
      _ = rs h₂ s₂ * 1 := by rw [ha, hb, mul_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

end

section
variable {K : Type} [CommRing K] {X : Sch K}

private theorem secRes_eq {U V : X.left.Opens} (h : V ≤ U) (x : Sec X U) :
    secRes X h x = rs h x := by
  change (Scheme.Hom.appLE (𝟙 X.left) U V h).hom x = _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

private abbrev Idx (J : X.left.IdealSheafData) : Type :=
  Σ V : X.left.affineOpens, {s : Γ(X.left, V.1) // J.ideal V = Ideal.span {s} ∧ s ∈ nonZeroDivisors Γ(X.left, V.1)}

private abbrev idxU (J : X.left.IdealSheafData) (j : Idx J) : X.left.Opens := j.1.1

private theorem aff2 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_two]
  rw [this]
  exact (i 0).1.2.inf (i 1).1.2

private theorem aff3 [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    IsAffineOpen (cap (X := X) (idxU J) i) := by
  have : cap (X := X) (idxU J) i = idxU J (i 0) ⊓ idxU J (i 1) ⊓ idxU J (i 2) := by
    ext x
    simp [mem_inter_iff, Fin.forall_fin_succ, and_assoc]
  rw [this]
  exact ((i 0).1.2.inf (i 1).1.2).inf (i 2).1.2

private theorem exists_g [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) :
    ∃ g : Γ(X.left, cap (X := X) (idxU J) i)ˣ, rs (inter_le (X := X.left.toTopCat) (idxU J) i 0) (i 0).2.1 =
      g.val * rs (inter_le (X := X.left.toTopCat) (idxU J) i 1) (i 1).2.1 :=
  exists_unit J (i 0).1.2 (i 1).1.2 (aff2 J i) _ _ (i 0).2.2.1 (i 1).2.2.1 (i 1).2.2.2

private def gg [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 2 → Idx J) : Γ(X.left, cap (X := X) (idxU J) i)ˣ :=
  (exists_g (X := X) J i).choose

private theorem gg_spec [X.left.IsSeparated] (J : X.left.IdealSheafData) {T : X.left.Opens} (j : Fin 2 → Idx J)
    (a c : Idx J) (ha : j 0 = a) (hc : j 1 = c) (hT : T ≤ cap (X := X) (idxU J) j) (ta : T ≤ idxU J a) (tc : T ≤ idxU J c) :
    rs ta a.2.1 = rs hT (gg (X := X) J j).val * rs tc c.2.1 := by
  subst ha hc
  have e := congrArg (rs hT) (exists_g (X := X) J j).choose_spec
  rw [map_mul, rs_rs, rs_rs] at e
  exact e

private theorem gg_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (i : Fin 3 → Idx J) :
    rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (gg (X := X) J (i ∘ Fin.succAbove 2)).val *
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (gg (X := X) J (i ∘ Fin.succAbove 0)).val =
      rs (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (gg (X := X) J (i ∘ Fin.succAbove 1)).val := by
  have t : ∀ a, cap (X := X) (idxU J) i ≤ idxU J (i a) := inter_le (X := X.left.toTopCat) (idxU J) i
  have A := gg_spec (X := X) J (i ∘ Fin.succAbove 2) (i 0) (i 1) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 2)) (t 0) (t 1)
  have B := gg_spec (X := X) J (i ∘ Fin.succAbove 0) (i 1) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 0)) (t 1) (t 2)
  have C := gg_spec (X := X) J (i ∘ Fin.succAbove 1) (i 0) (i 2) rfl rfl
    (inter_le_comp (X := X.left.toTopCat) (idxU J) i (Fin.succAbove 1)) (t 0) (t 2)
  refine (mul_cancel_right_mem_nonZeroDivisors (nzd_rs (i 2).1.2 (aff3 J i) (t 2) (i 2).2.2.2)).1 ?_
  rw [← C, mul_assoc, ← B, ← A]

private theorem exists_coc [X.left.IsSeparated] (J : X.left.IdealSheafData) (hJ : IsLocallyGeneratedByNonZeroDivisor J) :
    ∃ (L : Coc X) (s : ∀ j : L.ι, Sec X (L.U j)) (a : ∀ j, IsAffineOpen (L.U j)),
      (∀ j, J.ideal ⟨L.U j, a j⟩ = Ideal.span {(s j : Γ(X.left, L.U j))}) ∧
      (∀ j, s j ∈ nonZeroDivisors (Sec X (L.U j))) ∧
      ∀ j : Fin 2 → L.ι, secRes X (inter_le (X := X.left.toTopCat) L.U j 0) (s (j 0)) =
        (L.g j).val * secRes X (inter_le (X := X.left.toTopCat) L.U j 1) (s (j 1)) := by
  refine ⟨{ ι := Idx J, U := idxU J, cov := ⟨fun j => j.1.2, ?_⟩, g := gg (X := X) J, coc := ?_ }, fun j => j.2.1,
    fun j => j.1.2, fun j => j.2.2.1, fun j => j.2.2.2, fun j => ?_⟩
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, f, hx, hf, e⟩ := hJ x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, f, e, hf⟩, hx⟩
  · intro i
    simp only [secRes_eq]
    exact gg_coc (X := X) J i
  · refine (secRes_eq _ _).trans (((exists_g (X := X) J j).choose_spec).trans ?_)
    exact congrArg (fun t => (gg (X := X) J j).val * t) (secRes_eq _ _).symm

end

theorem exDiv : ExDiv := by
  intro R _ _ Z W D _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth D Z.hom
  obtain ⟨hp, hcl, -⟩ := blOff R π hπ
  haveI : IsProper π.left := hp
  haveI : IsClosedImmersion (dg Z).left := by
    change IsClosedImmersion (pullback.diagonal Z.hom)
    infer_instance
  haveI : IsSeparated (XX Z).hom := by
    change IsSeparated (pullback.fst Z.hom Z.hom ≫ Z.hom)
    infer_instance
  haveI : IsSeparated W.hom := by
    rw [← Over.w π]
    infer_instance
  haveI : W.left.IsSeparated := by
    constructor
    have : terminal.from W.left = W.hom ≫ terminal.from _ := terminal.hom_ext _ _
    rw [this]
    infer_instance
  obtain ⟨L, s, a, h1, h2, h3⟩ := exists_coc (X := W) _ hπ.1
  haveI : IsClosedImmersion (exI π).left := hcl
  refine ⟨L, s, hcl, fun j => ?_, h2, h3⟩
  have e : (exI π).left.ker = (dg Z).left.ker.comap π.left :=
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (dg Z).left π.left
  have e2 := Scheme.Hom.ker_apply (exI π).left ⟨L.U j, a j⟩
  rw [e, h1 j] at e2
  refine Eq.trans ?_ e2.symm
  change RingHom.ker (Scheme.Hom.appLE (exI π).left (L.U j) _ le_rfl).hom = _
  rw [Scheme.Hom.appLE_eq_app]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdSmooth_of_bijective {A B σ : Type} [CommRing A] [CommRing B] [Fintype σ] {d : ℕ}
    (hd : Fintype.card σ = d) (φ : A →+* B) (y : σ → B)
    (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    φ.IsStandardSmoothOfRelativeDimension d := by
  have h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr
      (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)
  let e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A :=
    (MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv
  let e₂ : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  have hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A)) := by
    ext a
    simp [e₁, e₂, MvPolynomial.algebraMap_eq]
  rw [hφ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0

private theorem comap_surjective_of_bijective {A B σ : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y : σ → B) (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let e : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  let ρ : B →+* A := (MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom
  have hρ : ρ.comp φ = RingHom.id A := by
    ext a
    have : e.symm (φ a) = MvPolynomial.C a :=
      e.symm_apply_eq.2 (by simp [e])
    simp [ρ, this]
  intro p
  refine ⟨PrimeSpectrum.comap ρ p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]

private theorem exists_apply_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : Function.Surjective (PrimeSpectrum.comap (f.appLE U V e).hom)) {y : Y} (hy : y ∈ U) :
    ∃ x, f x = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hy
  obtain ⟨q, rfl⟩ := hs p
  refine ⟨hV.fromSpec q, ?_⟩
  have h := congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

private theorem isProper_snd {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (hf : IsProper f) :
    IsProper (pullback.snd f g) :=
  haveI := hf; inferInstance

private theorem exists_chart {R : Type} [CommRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
    [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z) (hπ : IsBl π) (z : Z.left) :
    ∃ (c : DChart Z (d + 1)) (_ : BChart π c.N c.s), (dg Z).left z ∈ c.N := by
  obtain ⟨U, u, hz, hc⟩ := coordEx R Z (d + 1) z
  obtain ⟨c, -, -, hN⟩ := (dChartEx R Z (d + 1)).1 U u hc z hz
  exact ⟨c, (blChart R π hπ (d + 1) c).some, hN⟩

theorem exSmooth : ExSmooth := by
  intro R _ _ Z W d _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom
  refine ⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ ((exG π).left x)
    have e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left := pullback.condition
    have hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N := by
      have h := congr($e x)
      simp only [Scheme.Hom.comp_apply] at h
      change π.left ((exI π).left x) ∈ c.N
      rw [h]
      exact hN
    rw [← b.cov] at hW
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b j
    exact ⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩
  · exact isProper_snd π.left (dg Z).left (blOff R π hπ).1
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ z
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b 0
    exact exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN

end UpperTheory.Gal.KunnethLefschetz.G
end
