import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ProjectiveProper

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi

theorem projProper : ProjProperSt :=
  fun _ _ _ _ h => GlobalTheory.CommonModel.isProper_of_isProjOver h

theorem abLocusOne : AbLocusOneSt := by
  rintro S G _ hG K _ t ht s ⟨p, rfl⟩ K' _ _ t' ⟨p', hp'⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := t') p p' hp'.symm
  let j := (pullback t t').fromSpecResidueField z
  let u := j ≫ pullback.fst t t'
  let u' := j ≫ pullback.snd t t'
  have e : u ≫ t = u' ≫ t' := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have P₂ := (IsPullback.of_hasPullback (pullback.snd G.hom t') u').paste_horiz (IsPullback.of_hasPullback G.hom t')
  rw [← e] at P₂
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t') u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd (pullback.snd G.hom t') u'),
      P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K') := inferInstanceAs (Subsingleton (PrimeSpectrum K'))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t') :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
