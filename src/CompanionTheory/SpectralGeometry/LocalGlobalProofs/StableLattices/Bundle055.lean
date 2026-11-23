module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
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
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe

@[expose] public section

section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CyclicScalar

theorem inner_map_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y

theorem map_inv_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have h : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

theorem orthogonal_stable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) (v : H) (hv : v ∈ Uᗮ) : σ g v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_inv_map σ g u, inner_map_map σ hσ]
  exact hv _ (hU _ _ hu)

theorem starProjection_commute {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) :
    U.starProjection * σ g = σ g * U.starProjection := by
  ext v
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : U.starProjection v ∈ U := Submodule.starProjection_apply_mem U v
  have h2 : v - U.starProjection v ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v) := by
    rw [← map_add (f := _)]; simp
  rw [h3, map_add (f := _), Submodule.starProjection_eq_self_iff.2 (hU g _ h1),
    (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]

theorem exists_isIrredSubrep : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W := by
  intro G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal
  haveI : CompleteSpace Q := hQ.completeSpace_coe

  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => σ g ξ)
  have hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
    intro g v hv
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact this hv
  have hW : IsSubrep σ S.topologicalClosure := isSubrep_topologicalClosure hSstable
  have horbit : ∀ g, σ g ξ ∈ S.topologicalClosure := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hξW : ξ ∈ S.topologicalClosure := by simpa using horbit 1

  have hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A := by
    intro A hA h
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA
    rintro _ ⟨g, rfl⟩
    exact h g

  have hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ) := by
    have hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous
    refine fun w hw => hmin _ hclosed (fun g => ?_) hw
    obtain ⟨c, hc⟩ := hscal g
    have e : σ g ξ = c • ξ + (σ g ξ - c • ξ) := by abel
    change Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)
    rw [e, map_add (f := _), (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul,
      Submodule.starProjection_eq_self_iff.2 hξQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)
  refine ⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩
  haveI : CompleteSpace U := hU.1.completeSpace_coe
  have hPc := starProjection_commute σ hσ U hU.2
  have hPQ : U.starProjection ξ ∈ Q := hcomm _ hPc ξ hξQ
  have hPU : U.starProjection ξ ∈ U := Submodule.starProjection_apply_mem U ξ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by
    have := hline _ (hUW hPU)
    rw [Submodule.starProjection_eq_self_iff.2 hPQ] at this
    exact Submodule.mem_span_singleton.1 this
  have hcc : c * c = c := by
    have h1 : U.starProjection (c • ξ) = c • ξ := by
      rw [hc]; exact Submodule.starProjection_eq_self_iff.2 hPU
    rw [map_smul, ← hc, smul_smul] at h1
    have h2 : (c * c - c) • ξ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc]; ring
    exact (mul_eq_zero.1 this).imp id sub_eq_zero.1
  rcases hc01 with rfl | rfl
  · left
    have hP0 : U.starProjection ξ = 0 := by rw [← hc, zero_smul]
    have hle : S.topologicalClosure ≤ Uᗮ := by
      refine hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_
      refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
      have := DFunLike.congr_fun (hPc g) ξ
      simpa [hP0] using this
    refine (Submodule.eq_bot_iff U).2 fun x hx => ?_
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)
  · right
    have hξU : ξ ∈ U := by
      rw [one_smul] at hc
      rw [hc]; exact hPU
    exact le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)

end GlobalTheory.CompanionTheory.CyclicScalar
end

section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DirectFactor

theorem bicommutant_restriction_prime :
    ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0 := by
  intro G G₁ H _ _ _ _ π hπ j p hp hc x y hy hy0 hxy
  let W₀ : Submodule ℂ H := Submodule.span ℂ (Set.range fun q : G₁ × H => π (j q.1) (y q.2))
  have hgen : ∀ (g' : G₁) (h : H), π (j g') (y h) ∈ W₀ := fun g' h =>
    Submodule.subset_span ⟨(g', h), rfl⟩
  have hinv : ∀ g, ∀ v ∈ W₀, π g v ∈ W₀ := by
    intro g v hv
    obtain ⟨k, hk, hg⟩ : ∃ k, p k = 1 ∧ g = j (p g) * k :=
      ⟨(j (p g))⁻¹ * g, by simp [hp], by simp⟩
    have hpg : π g = π (j (p g)) * π k := by
      have := congrArg π hg
      rwa [map_mul] at this
    have hKB : ∀ g', π k * π (j g') = π (j g') * π k := fun g' => by
      rw [← map_mul, ← map_mul, (hc g' k hk).eq]
    have hKy : π k * y = y * π k := hy (π k) hKB
    have a1 : ∀ v, π k (y v) = y (π k v) := fun v => DFunLike.congr_fun hKy v
    have a2 : ∀ g' v, π k (π (j g') v) = π (j g') (π k v) := fun g' v =>
      DFunLike.congr_fun (hKB g') v
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g', h⟩, rfl⟩ := hv
      have e : π g (π (j g') (y h)) = π (j (p g * g')) (y (π k h)) := by
        rw [hpg, map_mul, map_mul]
        simp only [ContinuousLinearMap.mul_apply, a1, a2]
      simpa only [e] using hgen (p g * g') (π k h)
    | zero => simp
    | add u w _ _ hu hw => simpa only [map_add (f := _)] using W₀.add_mem hu hw
    | smul c u _ hu => simpa only [map_smul] using W₀.smul_mem c hu
  have hker : W₀.topologicalClosure ≤ LinearMap.ker (x : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker x)
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g', h⟩, rfl⟩
    exact DFunLike.congr_fun (hxy g') h
  rcases hπ.2 _ (isSubrep_topologicalClosure hinv) with hbot | htop
  · exfalso
    apply hy0
    ext h
    have hm : y h ∈ W₀.topologicalClosure := by
      apply Submodule.le_topologicalClosure
      simpa using hgen 1 h
    rw [hbot] at hm
    simpa using hm
  · ext h
    have hm : h ∈ W₀.topologicalClosure := by rw [htop]; trivial
    simpa using hker hm

end GlobalTheory.CompanionTheory.DirectFactor
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

variable {S : Scheme.{0}} {A X Y : Over S} [GrpObj A]

theorem val_lift_eq_of_comp_eq (hA : IsAbelianScheme A) (q : X ⟶ Y) {N : LB (A ⊗ Y).left} (hN : N.IsLB)
    (r : LB.Gen (ev N (1 : Y ⟶ A) (𝟙 Y)))
    (t : LB.Gen (ev N (fst A X) (snd A X ≫ q))) (ht : t.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (s : Z ⟶ X.left) (z : Z) (J : (Z ⟶ (A ⊗ Y).left) → N.ι), Good N z J →
      val t (s ≫ (lift (1 : X ⟶ A) (𝟙 X)).left) z J = val r (s ≫ q.left) z J)
    {T : Over S} (α : T ⟶ A) (x x' : T ⟶ X) (h : x ≫ q = x' ≫ q)
    (z : T.left) (J : (T.left ⟶ (A ⊗ Y).left) → N.ι) (hJ : Good N z J) :
    val t (lift α x).left z J = val t (lift α x').left z J := by
  have hc : ∀ x₁ : T ⟶ X, lift (fst A T) (snd A T ≫ x₁) ≫ lift (fst A X) (snd A X ≫ q) =
      lift (fst A T) (snd A T ≫ x₁ ≫ q) := fun x₁ => by
    ext <;> simp
  have hc' : (lift (fst A T) (snd A T ≫ x)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      (lift (fst A T) (snd A T ≫ x')).left ≫ (lift (fst A X) (snd A X ≫ q)).left := by
    rw [← Over.comp_left, ← Over.comp_left, hc, hc, h]
  have he : (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (snd A T).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hs : ∀ x₁ : T ⟶ X, (lift (1 : T ⟶ A) (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left =
      x₁.left ≫ (lift (1 : X ⟶ A) (𝟙 X)).left := fun x₁ => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hv : ∀ x₁ : T ⟶ X, ∀ (y : T.left) (I : (T.left ⟶ (A ⊗ Y).left) → N.ι), Good N y I →
      val (LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x₁)).left) (lift (1 : T ⟶ A) (𝟙 T)).left y I =
        val r (x₁ ≫ q).left y I := fun x₁ y I hI => by
    rw [val_pull hI, hs, hn _ _ _ _ hI, Over.comp_left]
  have key := gen_unique' hN (u := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x)).left)
    (u' := LB.pullGen N _ _ t (lift (fst A T) (snd A T ≫ x')).left)
    (fun U _ k => by simp only [hc']) (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left he
    (surj_snd GlobalTheory.globalFns_holds hA T)
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _)
    (fun y I hI => by rw [hv x y I hI, hv x' y I hI, h]) T.left (lift α (𝟙 T)).left z J hJ
  have hl : ∀ x₁ : T ⟶ X, (lift α (𝟙 T)).left ≫ (lift (fst A T) (snd A T ≫ x₁)).left = (lift α x₁).left := fun x₁ => by
    rw [← Over.comp_left]
    congr 1
    ext <;> simp
  rw [val_pull hJ, val_pull hJ, hl, hl] at key
  exact key

end GlobalTheory.CompanionTheory.RigDesc

namespace GlobalTheory.CompanionTheory.RigDesc

theorem triv_of_triv_of_flat_cover : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → Triv (ev N (fst A X) (snd A X ≫ q)) → Triv N := by
  rintro S A X Y _ hA q hfl hlfp hsj N hN ⟨r, hr⟩ ⟨t₀, ht₀⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hfl hlfp hsj
  have he : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (snd A X).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hef : (lift (1 : X ⟶ A) (𝟙 X)).left ≫ (lift (fst A X) (snd A X ≫ q)).left =
      q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  obtain ⟨t, ht, hn⟩ := GlobalTheory.T.linear_combination_generator_section_exists hN (fun _ => (lift (fst A X) (snd A X ≫ q)).left) (fun _ => 1)
    (fun _ => q.left ≫ (lift (1 : Y ⟶ A) (𝟙 Y)).left) (fun _ => 1) (snd A X).left (lift (1 : X ⟶ A) (𝟙 X)).left he
    (fun U _ k => by simp only [hef]) t₀ ht₀ (LB.pullGen N _ _ r q.left) (DVR.pullGen_isGen _ _ _ _ hr _)
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator _ f₁ f₂ f₃ N hN t ht ?_
  intro W a b hab w i hi
  have hw : a ≫ (A ⊗ X).hom = b ≫ (A ⊗ X).hom := by
    have e := congrArg (· ≫ (A ⊗ Y).hom) hab
    simpa only [Category.assoc, Over.w] using e
  let T : Over S := Over.mk (a ≫ (A ⊗ X).hom)
  let a' : T ⟶ A ⊗ X := Over.homMk a rfl
  let b' : T ⟶ A ⊗ X := Over.homMk b hw.symm
  have hab' : a' ≫ lift (fst A X) (snd A X ≫ q) = b' ≫ lift (fst A X) (snd A X ≫ q) := by
    exact Over.OverMorphism.ext hab
  have h₁ : a' ≫ fst A X = b' ≫ fst A X := by
    have e := congrArg (· ≫ fst A Y) hab'
    simpa using e
  have h₂ : (a' ≫ snd A X) ≫ q = (b' ≫ snd A X) ≫ q := by
    have e := congrArg (· ≫ snd A Y) hab'
    simpa using e
  obtain ⟨J, hJ, hJi⟩ := exists_good N hN w (K := PUnit.{1}) (fun _ => a ≫ (lift (fst A X) (snd A X ≫ q)).left)
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have hJi' : J (a ≫ (lift (fst A X) (snd A X ≫ q)).left) = i := hJi PUnit.unit
  have key := val_lift_eq_of_comp_eq hA q hN r t ht (fun Z s z I hI => (hn Z s z I hI).trans (val_pull hI _ _ _))
    (a' ≫ fst A X) (a' ≫ snd A X) (b' ≫ snd A X) h₂ w J hJ
  have ea : (lift (a' ≫ fst A X) (a' ≫ snd A X)).left = a := by
    rw [← comp_lift, lift_fst_snd]; simp [a']
  have eb : (lift (a' ≫ fst A X) (b' ≫ snd A X)).left = b := by
    rw [h₁, ← comp_lift, lift_fst_snd]; simp [b']
  rw [ea, eb, val_of t a w J (fun _ => i) (fun _ => hJi'), val_of t b w J (fun _ => i) (fun _ => by rw [← hab]; exact hJi')] at key
  exact key


end GlobalTheory.CompanionTheory.RigDesc
end
