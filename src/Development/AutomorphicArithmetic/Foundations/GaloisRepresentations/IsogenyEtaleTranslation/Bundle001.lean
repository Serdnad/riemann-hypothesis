module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descFin_of : DescFin := by
  intro A B C c f hc hs he hfin
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective c f
  have : IsProper f := { }
  have : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end UpperTheory.Gal.FixZ
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace UpperTheory.Gal.FixZ

section Coord

variable {C : Type*} [Category C] {A : C} {k : ℕ} [HasProduct (fun _ : Fin k => A)]

private noncomputable def coordMap (j : Fin k) (φ : A ⟶ A) :
    (∏ᶜ fun _ : Fin k => A) ⟶ ∏ᶜ fun _ : Fin k => A :=
  Pi.lift fun i => if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i

private lemma coordMap_π (j i : Fin k) (φ : A ⟶ A) :
    coordMap j φ ≫ Pi.π (fun _ : Fin k => A) i =
      if i = j then Pi.π (fun _ : Fin k => A) j ≫ φ else Pi.π (fun _ : Fin k => A) i := by
  simp [coordMap]

private lemma coordMap_isPullback (j : Fin k) (φ : A ⟶ A) :
    IsPullback (coordMap j φ) (Pi.π (fun _ : Fin k => A) j) (Pi.π (fun _ : Fin k => A) j) φ := by
  refine ⟨⟨by simp [coordMap_π]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Pi.lift fun i => if i = j then s.snd else s.fst ≫ Pi.π (fun _ : Fin k => A) i)
    ?_ ?_ ?_⟩⟩
  · intro s
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, coordMap_π]
    by_cases h : i = j
    · subst h
      simpa using s.condition.symm
    · simp [h]
  · intro s
    simp
  · intro s m h₁ h₂
    refine Pi.hom_ext _ _ fun i => ?_
    by_cases h : i = j
    · subst h
      simpa using h₂
    · have := congrArg (· ≫ Pi.π (fun _ : Fin k => A) i) h₁
      simpa [coordMap_π, h] using this

end Coord

private lemma pow_prop (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{0}} (A : Over S) (k : ℕ) (f : Fin k → (A ⟶ A))
    (hf : ∀ i, P (f i).left) (g : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k)
    (hg : ∀ i, g ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ f i) : P g.left := by
  have step : ∀ j : ℕ, j ≤ k → ∃ h : GlobalTheory.KS.pow A k ⟶ GlobalTheory.KS.pow A k, P h.left ∧
      ∀ i : Fin k, h ≫ GlobalTheory.KS.pr A i =
        if i.val < j then GlobalTheory.KS.pr A i ≫ f i else GlobalTheory.KS.pr A i := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨𝟙 _, by simpa using P.id_mem _, fun i => by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨h, hP, hh⟩ := ih (by omega)
      let j' : Fin k := ⟨j, by omega⟩
      have hb : IsPullback (coordMap j' (f j')).left (GlobalTheory.KS.pr A j').left
          (GlobalTheory.KS.pr A j').left (f j').left :=
        (coordMap_isPullback j' (f j')).map (Over.forget S)
      have he : P (coordMap j' (f j')).left := P.of_isPullback hb.flip (hf j')
      refine ⟨h ≫ coordMap j' (f j'), ?_, fun i => ?_⟩
      · rw [Over.comp_left]
        exact P.comp_mem _ _ hP he
      · rw [Category.assoc, GlobalTheory.KS.pr, coordMap_π]
        by_cases hi : i = j'
        · subst hi
          have h0 : h ≫ Pi.π (fun _ : Fin k => A) j' = Pi.π (fun _ : Fin k => A) j' := by
            have := hh j'
            simpa [GlobalTheory.KS.pr, j'] using this
          rw [if_pos rfl, if_pos (by simp [j']), ← Category.assoc, h0]
        · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
          have := hh i
          simp only [GlobalTheory.KS.pr] at this
          simp only [hi, if_false, this]
          by_cases hlt : i.val < j
          · simp [hlt, Nat.lt_succ_of_lt hlt]
          · have : ¬ i.val < j + 1 := by omega
            simp [hlt, this]
  obtain ⟨h, hP, hh⟩ := step k le_rfl
  have : g = h := Pi.hom_ext _ _ fun i => by
    have := hh i
    simp only [i.isLt, if_true] at this
    exact (hg i).trans this.symm
  rw [this]
  exact hP

theorem powFEt_of : PowFEt := by
  intro S A k f hf g hg
  exact ⟨pow_prop @IsFinite A k f (fun i => (hf i).1) g hg,
    pow_prop @Etale A k f (fun i => (hf i).2.1) g hg,
    pow_prop @Surjective A k f (fun i => (hf i).2.2) g hg⟩

end UpperTheory.Gal.FixZ
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Integ)

namespace UpperTheory.Gal.FixZ

private lemma tr_comp {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : G3.Tower B Γ) {i j m : X.ι} {h h' g : Γ} (a b a' b')
    (e : h' * h = g) (c d) : X.tr i j h a b ≫ X.tr j m h' a' b' = X.tr i m g c d := by
  subst e
  exact X.tr_mul i j m h h' a b a' b' c d

private lemma lofp_cancel {A B S : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW : U ≤ g ⁻¹ᵁ W⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open hxW (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, RingHom.FinitePresentation.of_comp_finiteType
    (g.appLE W U hUW).hom ?_ (g.finiteType_appLE hW hU hUW)⟩
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (f ≫ g).finitePresentation_appLE hW hV _

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {gb : GBase D.toG ℂ} {k : ℕ}

private lemma q_props (hP : G3.PowSm) (T : KS L gb k) (N : Lv p) :
    Smooth (T.X.q (T.lev N)) ∧ IsSeparated (T.X.q (T.lev N)) := by
  obtain ⟨h1, h2, -⟩ := hP p D ℂ gb N (T.M N) k
  rw [← T.e_q N]
  exact ⟨inferInstance, inferInstance⟩

private lemma tr_props (hP : G3.PowSm) (T : KS L gb k) (N' N : Lv p) (h : G.GAf) (a b) :
    IsSeparated (T.X.tr (T.lev N') (T.lev N) h a b) ∧ LocallyOfFinitePresentation (T.X.tr (T.lev N') (T.lev N) h a b) := by
  obtain ⟨s1, s2⟩ := q_props hP T N'
  obtain ⟨s3, s4⟩ := q_props hP T N
  have e := T.X.tr_q (T.lev N') (T.lev N) h a b
  constructor
  · rw [← e] at s2
    exact IsSeparated.of_comp _ (T.X.q (T.lev N))
  · rw [← e] at s1
    exact lofp_cancel _ (T.X.q (T.lev N))

private lemma scal_fe (hS : TrScal) (T : KS L gb k) (P Q : Lv p) (d : ℕ) (z : G.GAf) (hd : 0 < d) (hc : d.Coprime p)
    (hz : IsScal L d z) (a b) (a₁ : (1 : G.GAf) ∈ T.X.Δ)
    (b₁ : ∀ u ∈ T.X.K (T.lev P), 1 * u * 1⁻¹ ∈ T.X.K (T.lev Q)) (a₂ : z ∈ T.X.Δ)
    (b₂ : ∀ u ∈ T.X.K (T.lev Q), z * u * z⁻¹ ∈ T.X.K (T.lev Q)) :
    IsFinite (T.X.tr (T.lev P) (T.lev Q) z a b) ∧ Etale (T.X.tr (T.lev P) (T.lev Q) z a b) := by
  have e := tr_comp T.X a₁ b₁ a₂ b₂ (mul_one z) a b
  obtain ⟨f1, f2⟩ := hS p D G L gb k T Q d z hd hc hz a₂ b₂
  have f3 := T.X.fin _ _ a₁ b₁
  have f4 := T.X.etale _ _ a₁ b₁
  rw [← e]
  exact ⟨inferInstance, inferInstance⟩

theorem trFEt_of : G3.PowSm → ScalEx → TrScal → EtCancel → DescEt → DescFin → TrFEt := by
  classical
  intro hP hSc hTS hEC hDE hDF p _ D G L gb k T N' N h a b
  obtain ⟨d, z, hd, hc, hz, hzi, hzh⟩ := hSc p D G L h ((T.Δ_eq h).1 a)
  have hcen := hz.1
  have zΔ : z ∈ T.X.Δ := (T.Δ_eq z).2 hzi
  have h'Δ : z * h⁻¹ ∈ T.X.Δ := (T.Δ_eq _).2 hzh
  have oΔ : (1 : G.GAf) ∈ T.X.Δ := one_mem _
  have zc : ∀ u : G.GAf, z * u * z⁻¹ = u := fun u => by rw [hcen u, mul_inv_cancel_right]
  have e1 : h * (z * h⁻¹) = z := by rw [← mul_assoc, ← hcen h, mul_inv_cancel_right]
  have e2 : z * h⁻¹ * h = z := by rw [inv_mul_cancel_right]

  obtain ⟨m, -, -, hm⟩ := T.X.deep (T.lev N') {(T.lev N, 1), (T.lev N', z * h⁻¹)}
  obtain ⟨m', -, -, hm'⟩ := T.X.deep (T.lev N') {(m, h), (T.lev N', 1)}
  obtain ⟨M, rfl⟩ := T.lev.surjective m
  obtain ⟨M', rfl⟩ := T.lev.surjective m'
  have b1 : ∀ u ∈ T.X.K (T.lev M), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N) := hm (T.lev N, 1) (by simp)
  have b2 : ∀ u ∈ T.X.K (T.lev M), z * h⁻¹ * u * (z * h⁻¹)⁻¹ ∈ T.X.K (T.lev N') := hm (T.lev N', z * h⁻¹) (by simp)
  have b3 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev M) := hm' (T.lev M, h) (by simp)
  have b4 : ∀ u ∈ T.X.K (T.lev M'), 1 * u * 1⁻¹ ∈ T.X.K (T.lev N') := hm' (T.lev N', 1) (by simp)
  have b5 : ∀ u ∈ T.X.K (T.lev M), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 u hu
    simpa [zc] using this
  have b6 : ∀ u ∈ T.X.K (T.lev M'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by
    have := b4 u hu
    simpa [zc] using this
  have b7 : ∀ u ∈ T.X.K (T.lev N), z * u * z⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by rwa [zc]
  have b8 : ∀ u ∈ T.X.K (T.lev N'), z * u * z⁻¹ ∈ T.X.K (T.lev N') := fun u hu => by rwa [zc]
  have b9 : ∀ u ∈ T.X.K (T.lev M'), h * u * h⁻¹ ∈ T.X.K (T.lev N) := fun u hu => by
    have := b1 _ (b3 u hu)
    simpa using this

  have c1 : T.X.tr _ _ (z * h⁻¹) h'Δ b2 ≫ T.X.tr _ _ h a b = T.X.tr _ _ z zΔ b5 :=
    tr_comp T.X h'Δ b2 a b e1 zΔ b5
  have c2 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ (z * h⁻¹) h'Δ b2 = T.X.tr _ _ z zΔ b6 :=
    tr_comp T.X a b3 h'Δ b2 e2 zΔ b6
  obtain ⟨f1, f2⟩ := scal_fe hTS T M N d z hd hc hz zΔ b5 oΔ b1 zΔ b7
  obtain ⟨f3, f4⟩ := scal_fe hTS T M' N' d z hd hc hz zΔ b6 oΔ b4 zΔ b8
  rw [← c1] at f1 f2
  rw [← c2] at f3 f4
  obtain ⟨-, s1⟩ := tr_props hP T M N' (z * h⁻¹) h'Δ b2
  have t1 : LocallyOfFiniteType (T.X.tr _ _ (z * h⁻¹) h'Δ b2) := inferInstance
  obtain ⟨f5, f6⟩ := hEC _ _ _ _ (T.X.tr _ _ h a b3) (T.X.tr _ _ (z * h⁻¹) h'Δ b2) (T.X.tr _ _ h a b) t1 f3 f4 f1 f2

  have c3 : T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b = T.X.tr _ _ h a b9 :=
    tr_comp T.X oΔ b4 a b (mul_one h) a b9
  have c4 : T.X.tr _ _ h a b3 ≫ T.X.tr _ _ 1 oΔ b1 = T.X.tr _ _ h a b9 :=
    tr_comp T.X a b3 oΔ b1 (one_mul h) a b9
  have g1 := T.X.fin _ _ oΔ b1
  have g2 := T.X.etale _ _ oΔ b1
  have g3 : IsFinite (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  have g4 : Etale (T.X.tr _ _ 1 oΔ b4 ≫ T.X.tr _ _ h a b) := by
    rw [c3, ← c4]; infer_instance
  obtain ⟨s2, s3⟩ := tr_props hP T N' N h a b
  have g5 := hDE _ _ _ _ _ (T.X.etale _ _ oΔ b4) (T.X.onto _ _ oΔ b4) s3 g4
  exact ⟨hDF _ _ _ _ _ (T.X.onto _ _ oΔ b4) s2 g5 g3, g5⟩

end UpperTheory.Gal.FixZ

end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

private lemma relDim_eq_of_ringHom {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    {m n : ℕ} (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  letI := f.toAlgebra
  have e₁ : Module.rank S Ω[S⁄R] = m :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm
  have e₂ : Module.rank S Ω[S⁄R] = n :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn
  exact_mod_cast e₁.symm.trans e₂

private lemma exists_nontrivial_away {S : Type} [CommRing S] [Nontrivial S] (s : Set S)
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, Nontrivial (Localization.Away t) := by
  by_contra hne
  push_neg at hne
  have hsub : s ⊆ nilradical S := by
    intro t ht
    haveI : Subsingleton (Localization.Away t) := hne t ht
    have h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0 :=
      Subsingleton.elim _ _
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by simpa using hc'⟩
  have hle := Ideal.span_le.2 hsub
  rw [hs, top_le_iff] at hle
  have h1 : (1 : S) ∈ nilradical S := hle ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := h1
  simp at hk

private lemma relDim_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) (x : X) : m = n := by
  obtain ⟨U, hU, V, hV, hx, e, hmU⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hst⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨t, ht, hnt⟩ := exists_nontrivial_away s hs
  have hm' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
    (Localization.Away t) t _ hmU
  exact relDim_eq_of_ringHom _ hm' (hst t ht)

theorem dimUniq_of : DimUniq := by
  intro Z s d d' hd hd' hZ
  obtain ⟨z⟩ := hZ
  exact relDim_eq s hd hd' z

end UpperTheory.Gal.FixZ
end

section

open NumberField Polynomial GlobalTheory.UPel.HT GlobalTheory.LKGeo GlobalTheory.LKTrip

namespace UpperTheory.Gal.FixZ

variable {p : ℕ} [Fact p.Prime]

private lemma conj_ne (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hroot := D.ρc_root
  rw [hre] at hroot
  have hr : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by
    exact_mod_cast hroot
  have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

private lemma tr_eq_re (D : Datum p) : (D.tr : ℂ) = D.ρc + (starRingEnd ℂ) D.ρc := by
  have hne : D.ρc - (starRingEnd ℂ) D.ρc ≠ 0 := sub_ne_zero.mpr (Ne.symm (conj_ne D))
  have h1 := D.ρc_root
  have h2 : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) h1
    simpa using this
  apply mul_left_cancel₀ hne
  linear_combination h2 - h1

private lemma eps_eq (D : Datum p) : W2.epsD D = LocalSmoothExtension.epsOf D := by
  funext τ
  have hω : ((D.ω : D.F)) ^ 2 - (D.tr : D.F) * (D.ω : D.F) + (D.nm : D.F) = 0 := by
    have h1 : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have h2 := congrArg (algebraMap (𝓞 D.F) D.F) h1
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using h2
  have hτ : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg τ hω
    simpa using this
  have hfac : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    have h1 := D.ρc_root
    have h2 := tr_eq_re D
    rw [h2] at h1 hτ
    linear_combination hτ - h1
  unfold W2.epsD LocalSmoothExtension.epsOf
  by_cases h : τ (D.ω : D.F) = D.ρc
  · have : τ (D.ω : D.F) ≠ (starRingEnd ℂ) D.ρc := by
      rw [h]; exact Ne.symm (conj_ne D)
    simp [h, Ne.symm (conj_ne D)]
  · have h' : τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
      rcases mul_eq_zero.mp hfac with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) h
      · exact sub_eq_zero.mp h0
    rw [if_neg h, if_pos h']

private lemma map_inv {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : K[X]) :
    (W2.invPoly P).map f = LocalSmoothExtension.invPol (P.map f) := by
  unfold W2.invPoly LocalSmoothExtension.invPol
  rw [Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.coeff_map]
  congr 1
  simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]

private lemma kap_iff {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) :
    (∀ x, v.embedding (L.e x) = D.tau i₀ x) ↔ v.embedding (L.e (D.ω : D.F)) = D.ρc := by
  refine ⟨fun h => (h _).trans (D.tau_ω i₀), fun h => ?_⟩
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i₀ := by
    haveI : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hii
  have hs : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = D.tau i x := fun x => L.s_C i x
  rcases InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i)) with e | e
  · intro x
    rw [hi, e]
    exact hs x
  · exfalso
    rw [hi, e, ComplexEmbedding.conjugate_coe_eq, hs, D.tau_ω] at h
    exact conj_ne D h

private lemma kap_eq {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (μ : ℂ) :
    (W2.kap L v (D.tau i₀) μ)⁻¹ = LocalSmoothExtension.markOf L v μ := by
  unfold W2.kap LocalSmoothExtension.markOf
  by_cases h : v.embedding (L.e (D.ω : D.F)) = D.ρc
  · rw [if_pos ((kap_iff L ha i₀ v hv).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((kap_iff L ha i₀ v hv).mp h')), if_neg h]

end UpperTheory.Gal.FixZ

theorem UpperTheory.Gal.FixZ.wtEq_of :
    UpperTheory.Gal.FixZ.WtEq := by
  intro p _ D G L ha i₀ v hv k α y
  funext P μ
  unfold UpperTheory.Gal.W2.wtFix UpperTheory.Gal.LocalSmoothExtension.cW UpperTheory.Gal.LocalSmoothExtension.endPol
  rw [UpperTheory.Gal.FixZ.eps_eq, UpperTheory.Gal.FixZ.map_inv, UpperTheory.Gal.FixZ.kap_eq L ha i₀ v hv μ]
end

section

open AlgebraicGeometry in
theorem UpperTheory.Gal.FixZ.etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField

namespace UpperTheory.Gal.FixZ

theorem legOf_of : LegOf := by
  intro p _ D G L gb k T N' N h b
  obtain ⟨π, o, ψ, φ, hw, hs, htr, he⟩ := T.tr_eq N' N h b.1 b.2
  refine ⟨W2.Leg.mk π o ψ φ hs ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.2⟩, he, fun α => ?_⟩
  simp only [LocalSmoothExtension.leg, LocalSmoothExtension.al, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]
  rfl

end UpperTheory.Gal.FixZ

end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.FixZ

theorem descEt_of : DescEt := by
  intro A B C c f hc hs hf hcf
  exact GlobalTheory.etale_of_comp_of_etale_of_surjective c f

end UpperTheory.Gal.FixZ
end
