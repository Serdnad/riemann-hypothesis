import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.Model

variable {Z : Scheme.{0}} (G : Over Z) (A : LB Z) (N : ℕ)

alias snd_hom := Frames.snd_hom
alias mem_chart := Frames.mem_chart

def IsChartFrame (T : Over Z) (i : A.ι) (e : LB.Sec (LPow G (A.pull G.hom) (N : ℤ) T)) : Prop :=
  ∀ (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (y : Y) (J), Good (A.pull G.hom) y J →
    sval (L := A.pull G.hom) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) e r y J =
      (gm (r ≫ (snd T G).left ≫ G.hom) y _ (A.g (J (r ≫ (snd T G).left) PUnit.unit) i) ^ N).val

theorem exists_chartFrame (hA : A.IsLB) (T : Over Z) (i : A.ι) (hT : ∀ t, T.hom t ∈ A.U i) :
    ∃ e, IsChartFrame G A N T i e :=
  Frames.exists_chartFrame G A N hA T i hT

alias whisker_snd := Frames.whisker_snd

theorem IsChartFrame.pull {T T' : Over Z} (h : T' ⟶ T) {i : A.ι} {e} (he : IsChartFrame G A N T i e) (y : (T' ⊗ G).left) (J)
    (hJ : Good (A.pull G.hom) y J) :
    sval (L := A.pull G.hom) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) e (h ▷ G).left y J =
      (gm (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y _ (A.g (J (𝟙 _ ≫ (snd T' G).left) PUnit.unit) i) ^ N).val :=
  Frames.IsChartFrame.pull G A N h he y J hJ

theorem lin_of (hA : A.IsLB) {T T' : Over Z} (h : T' ⟶ T) {i j : A.ι} (hi : ∀ t, T'.hom t ∈ A.U i) (hj : ∀ t, T'.hom t ∈ A.U j)
    {e e'} (he : IsChartFrame G A N T j e) (he' : IsChartFrame G A N T' i e') (b : Fin 1 → _) (hb : b 0 = e)
    (c : Fin 1 → Γ(T'.left, ⊤))
    (hc : ∀ y, gs (fst T' G).left y ⊤ (c 0) = (gm (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y _ (A.g j i) ^ N).val) :
    Lin G (A.pull G.hom) N h b c e' :=
  Frames.lin_of G A N hA h hi hj he he' b hb c hc

theorem basisAlong_of (hA : A.IsLB) {T T' : Over Z} (h : T' ⟶ T) {i : A.ι} (hi : ∀ t, T'.hom t ∈ A.U i)
    (hb : Function.Bijective (fst T' G).left.appTop.hom) {e} (he : IsChartFrame G A N T i e) :
    BasisAlong G (A.pull G.hom) N h (fun _ : Fin 1 => e) :=
  Frames.basisAlong_of G A N hA h hi hb he

alias gs_unit_overlap := Frames.gs_unit_overlap
alias exists_ampFrames := Frames.exists_ampFrames
alias abLocus_eq_univ := Frames.abLocus_eq_univ
alias cDvr_padicInt := Frames.cDvr_padicInt

def constFamily (C : _root_.WeierstrassCurve ℤ) : Over (PSpace ℤ 1) :=
  Over.mk (pullback.snd (WeierstrassCurve.toSpec C) (PSpace.str ℤ 1))

theorem ampFrames_constFamily (C : _root_.WeierstrassCurve ℤ) :
    (∃ F : AmpFrames (constFamily C) ((ProjSpace.O1 ℤ 1).pull (constFamily C).hom) N, F.A = ProjSpace.O1 ℤ 1 ∧ F.n = 1) ∧
      abLocus (constFamily C) = Set.univ := by
  obtain ⟨⟨F, hA, hn, -⟩, hG⟩ := Frames.ampFrames_constFamily N C
  exact ⟨⟨F, hA, hn⟩, hG⟩

alias bijective_fst := Frames.bijective_fst
theorem exists_isFrame [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom] (hA : A.IsLB) (i : A.ι)
    (hi : ∀ z, z ∈ A.U i) {R₁ : Type} [CommRing R₁] [IsDomain R₁] (x : Sp (FractionRing R₁) ⟶ Z) :
    ∃ e, IsChartFrame G A N (Over.mk x) i e ∧ IsFrame G (A.pull G.hom) N x (fun _ : Fin 1 => e) :=
  Frames.exists_isFrame G A N hA i hi x

alias not_basisAlong_of_isEmpty := Frames.not_basisAlong_of_isEmpty
alias admissible_padicInt_maximalIdeal := Frames.admissible_padicInt_maximalIdeal
alias arcBase_examples := Frames.arcBase_examples

end GlobalTheory.LN.Model
end
