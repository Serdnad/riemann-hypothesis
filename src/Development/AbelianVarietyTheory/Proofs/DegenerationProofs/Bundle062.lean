module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle052
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Mathlib.CategoryTheory.MorphismProperty.Descent

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}
  {J : Type} {σ : J → H.Sec} {t : J → Ω}

theorem mem_nonzeroLocus_iff_div (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hg : ∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) (i : J) (z : M.Z) :
    z ∈ Out.nonzeroLocus (σ i) ↔ M.Div t i z := by
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
    obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
    have e := hv i l ⟨z, hzl⟩
    dsimp only at h0 h1
    rw [e] at h0 h1
    have hi : t i ≠ 0 := fun h => h0 (by rw [h, zero_div])
    refine ⟨hi, fun j => ?_⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (t i / d l)⁻¹ = t j / t i := by field_simp
    rwa [e'] at h3
  · intro hz
    have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i', hi', h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 ((isUnit_O_iff _).2 ?_)⟩
    dsimp only
    rw [hv i l ⟨z, hzl⟩]
    refine ⟨div_ne_zero hz.1 (hd.ne l), ?_⟩
    have h3 := mul_mem h1 (hz.2 i')
    have hi := hz.1
    have e' : d l / t i' * (t i' / t i) = (t i / d l)⁻¹ := by field_simp
    rwa [e'] at h3

theorem immBy_of_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  intro o Ω _ _ _ M H d J σ t k _ p ψ hH hd hv hg hp hU
  have key := mem_nonzeroLocus_iff_div hH hd hv hg
  refine ⟨top_unique fun z _ => ?_, fun i _ => ?_⟩
  · have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i, hi, h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨trivial, (key i z).2 ⟨hi, fun j => ?_⟩⟩⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (d l / t i) = t j / t i := by field_simp
    rwa [e'] at h3
  · have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
      have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
      subst this
      infer_instance
    have key' := key i
    generalize Out.nonzeroLocus (σ i) = W at key' ⊢
    by_cases hi : t i = 0
    · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
      subst hW
      refine ⟨isAffineOpen_bot _, fun _ => 0, fun j l => ?_,
        top_unique fun f _ => Subsingleton.elim 0 f ▸ zero_mem _⟩
      have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
      exact Subsingleton.elim _ _
    · obtain ⟨U, hUa, hUe, hR⟩ := hU i hi
      have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
      subst hWU
      have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
      have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
        (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
      choose r hr using hr
      refine ⟨hUa, r, fun j l => ?_, ?_⟩
      · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
        · have hl' : (H.U l : Set M.Z).Nonempty :=
            Set.Nonempty.mono (show (W ⊓ H.U l : M.Z.Opens) ≤ H.U l from inf_le_right) hl
          apply M.res_injective _ hl
          rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
            hv j l hl', hv i l hl', hr]
          have hdl := hd.ne l
          field_simp
        · have := hempty _ hl
          exact Subsingleton.elim _ _
      · refine top_unique fun f _ => ?_
        have h1 := hR _ ((mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩)
        have e : (Set.range ψ ∪ Set.range fun j => t j / t i) =
            M.res W hne '' (Set.range (constFn p W) ∪ Set.range r) := by
          rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
          congr 2
          · funext a
            exact ((M.res_apply W hne _).trans
              (valR_constFn_of_over p ψ M.pt hp W (M.top_le_preimage_pt hne) a)).symm
          · funext j
            exact ((M.res_apply W hne _).trans (hr j)).symm
        rw [e, ← RingHom.map_closure] at h1
        obtain ⟨g, hg1, hg2⟩ := h1
        have : g = f := M.res_injective W hne (hg2.trans (M.res_apply W hne f).symm)
        exact this ▸ hg1

end GlobalTheory.ZH.RatModel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtDescent

variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem hom_ext_of_points [Flat f] [Surjective f] {X Y : Over S₀} {a b : X ⟶ Y}
    (h : ∀ (T : Over S) (t : Over.mk (T.hom ≫ f) ⟶ X), t ≫ a = t ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  haveI := Flat.epi_of_flat_of_surjective (pullback.fst X.hom f)
  rw [← cancel_epi (pullback.fst X.hom f)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom f))
    (Over.homMk (pullback.fst X.hom f) (by simpa using pullback.condition)))

theorem isMonHom_of_grpPullback [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by
  have pa : ∀ {T : Over S} (x : T ⟶ X), pushHom hX T x ≫ g₀ = pushHom hY T (x ≫ g) := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, w, Category.assoc])
  have hm : μ[X₀] ≫ g₀ = (g₀ ⊗ₘ g₀) ≫ μ := by
    refine hom_ext_of_points (f := f) fun T t => ?_
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushHom hX T x) (pushHom hX T y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst]; exact hx.symm)
        (by rw [lift_snd]; exact hy.symm)
    rw [← Category.assoc, ← Hom.mul_def, ← map_mul, pa, lift_map_assoc, ← Hom.mul_def, pa, pa,
      ← map_mul, MonObj.mul_comp]
  refine ⟨?_, hm⟩
  have e : (η[X₀] ≫ g₀) * (η[X₀] ≫ g₀) = η[X₀] ≫ g₀ := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S₀) ⟶ X₀)
  have e' : η[X₀] ≫ g₀ = 1 := by simpa using e
  rw [e', Hom.one_def]; simp

theorem unit_comm {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀] {φ : X.left ⟶ X₀.left}
    (h : IsGrpPullback X X₀ f φ) : f ≫ (η[X₀]).left = (η[X]).left ≫ φ := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S))))
  have e₁ : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine Eq.symm (e.trans ?_)
  show (toUnit _ ≫ η[X₀]).left = _
  simp

theorem fpqc_of_isPullback [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩

theorem isPullback_of_baseChange [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by
  haveI : Flat τ := (fpqc_of_isPullback hτ).1.2
  haveI : Surjective τ := (fpqc_of_isPullback hτ).1.1
  haveI := Flat.epi_of_flat_of_surjective τ
  have w : i₀ ≫ q₀ = t₀ ≫ e₀ := by
    rw [← cancel_epi τ, reassoc_of% hi, hγ.w, reassoc_of% H.w, reassoc_of% hτ.w, he]
  let c : T₀ ⟶ pullback q₀ e₀ := pullback.lift i₀ t₀ w
  have c₁ : c ≫ pullback.fst q₀ e₀ = i₀ := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd q₀ e₀ = t₀ := pullback.lift_snd _ _ _
  have hp : IsPullback (τ ≫ c) t (pullback.snd q₀ e₀) f := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, c₂, hτ.w]) (IsPullback.of_hasPullback q₀ e₀)
    rw [Category.assoc, c₁, hi, he]
    exact H.paste_horiz hγ
  have hc : IsPullback τ (𝟙 T) c (τ ≫ c) := by
    refine IsPullback.of_bot ?_ (by simp) hp
    rw [c₂, Category.id_comp]
    exact hτ
  haveI : IsIso c := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip
    (fpqc_of_isPullback hp) (inferInstanceAs (IsIso (𝟙 T)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) c₁ c₂

end GlobalTheory.ExtDescent

namespace GlobalTheory

open ExtDescent

theorem splitTorus_extension_descends :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  intro k K _ _ β G B _ _ G₀ B₀ _ _ X _ φG φ hG hB q i q₀ i₀ wq wi hq hfl hsu hqc hi H
  haveI h₁ : Flat (spMap β) := inferInstance
  haveI h₂ : Surjective (spMap β) := inferInstance
  haveI h₃ : QuasiCompact (spMap β) := inferInstance
  have hγ : IsPullback φG q.left q₀.left φ := by
    refine IsPullback.of_bot ?_ wq hB.1
    rw [Over.w, Over.w]
    exact hG.1
  have hφ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) φ :=
    fpqc_of_isPullback hB.1
  haveI := flat_descendsAlong_fpqc
  haveI := quasiCompact_descendsAlong_fpqc.{0}
  have hT := SplitTorus.isGrpPullback_bcMap (spMap β) X
  refine ⟨isMonHom_of_grpPullback hG hB q q₀ wq,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hγ.flip hφ hfl,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hγ.flip hφ hsu,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) hγ.flip hφ hqc,
    isMonHom_of_grpPullback hT hG i i₀ wi, ?_⟩
  have H' : IsPullback i.left (splitTorus (Sp K) X).hom q.left (η[B]).left :=
    H.map (Over.forget _)
  have H₀ := isPullback_of_baseChange H' hT.1 hγ wi (unit_comm hB)
  exact IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext H₀.w) H₀

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.point_descends_to_valuationRing' : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  first | exact @GlobalTheory.point_descends_to_valuationRing | exact GlobalTheory.point_descends_to_valuationRing | (intros; apply GlobalTheory.point_descends_to_valuationRing <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.additive_points_descend_field_extension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  first | exact @GlobalTheory.PointDescent.additive_points_descend | exact GlobalTheory.PointDescent.additive_points_descend | (intros; apply GlobalTheory.PointDescent.additive_points_descend <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by
  first | exact @GlobalTheory.SS.TorOpen.exists_open_part | exact GlobalTheory.SS.TorOpen.exists_open_part | (intros; apply GlobalTheory.SS.TorOpen.exists_open_part <;> assumption)
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpFlatDesc

open GrpDense MorphismProperty

variable {Z U : Scheme.{0}}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst X.hom j)
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))


set_option backward.isDefEq.respectTransparency.types false in
theorem isProper_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have h₁ : UniversallyClosed g :=
    of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip hj inferInstance
  have h₂ : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hj inferInstance
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    @IsStableUnderBaseChange.inf _ _ _ _ (@IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance)
      inferInstance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @UniversallyClosed := universallyClosed_respectsIso
  have h₃ : UniversallyClosed (pullback.diagonal g) :=
    of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hj
      (show UniversallyClosed (pullback.diagonal f) from inferInstance)
  have h₄ : IsSeparated g :=
    ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩
  exact {}

theorem geometricallyConnected_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [hf : GeometricallyConnected f] : GeometricallyConnected g := by
  refine ⟨fun K _ y W a b hW => ?_⟩

  obtain ⟨p, -⟩ := (pullback.fst y j).surjective (Classical.arbitrary _)
  let r := (Limits.pullback y j).fromSpecResidueField p
  let s := r ≫ pullback.fst y j
  let t := r ≫ pullback.snd y j
  have hst : t ≫ j = s ≫ y := by simp only [t, s, Category.assoc, pullback.condition]
  have hs : Surjective s := inferInstance

  have hc : ConnectedSpace ↥(Limits.pullback f t) := pullback_of_geometrically hf.1 _ t

  have hout : IsPullback (pullback.fst f t ≫ φ) (pullback.snd f t) g (s ≫ y) := by
    rw [← hst]
    exact (IsPullback.of_hasPullback f t).paste_horiz h
  let q : Limits.pullback f t ⟶ W :=
    hW.lift (pullback.fst f t ≫ φ) (pullback.snd f t ≫ s) (by simpa only [Category.assoc] using hout.w)
  have hq : IsPullback q (pullback.snd f t) b s :=
    IsPullback.of_right (by rwa [hW.lift_fst]) (hW.lift_snd _ _ _) hW
  have hqs : Surjective q := MorphismProperty.of_isPullback hq.flip hs
  exact hqs.surj.connectedSpace q.continuous

theorem grpObj_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, rfl, rfl, rfl, ⟨GrpFlatDesc.hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)

theorem isAbelianScheme_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] [QuasiCompact j] (G : Over Z) (A : Over U)
    [GrpObj A] (hA : IsAbelianScheme A) (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G)
    (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G) (φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left) (h₂ : IsSquare φ φ₂)
    (hm : φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsAbelianScheme G ∧ IsGrpPullback A G j φ := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, -, -, -, hc, hp⟩ := grpObj_of_flat_cover j G A φ h m i e (fun ψ hψ => by
    obtain rfl : ψ = φ₂ := Over.tensorObj_ext _ _ (hψ.1.trans h₂.1.symm) (hψ.2.trans h₂.2.symm)
    exact hm) hi he
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨inferInstance, ⟨hc, of_isPullback_of_descendsAlong (P := @Smooth) h.flip hj hA.smooth,
    isProper_of_isPullback h, geometricallyConnected_of_isPullback h⟩, hp⟩

end GlobalTheory.GrpFlatDesc

namespace GlobalTheory

theorem isAbelianScheme_descends_subfield :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  intro k K _ _ β B _ B₀ φ hB h m i e φ₂ h₁ h₂ hm hi he
  have : Flat (spMap β) := by
    algebraize [β]
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have : Surjective (spMap β) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GrpFlatDesc.isAbelianScheme_of_flat_cover (spMap β) B₀ B hB φ h m i e φ₂ ⟨h₁, h₂⟩ hm hi he

end GlobalTheory
end
end
