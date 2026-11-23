module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpansionLinear

section General

variable {X Y Y' : Scheme.{0}}

def secComb {L : LB X} {I : Type} [Fintype I] (c : I → Γ(X, ⊤)) (s : I → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (s i).f j
  compat := fun j j' => by

    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (s i)).compat j j'

theorem resTop_mul (W : X.Opens) (a b : Γ(X, ⊤)) : resTop W (a * b) = resTop W a * resTop W b := by
  simp only [resTop, map_mul]

theorem app_resTop (h : Y ⟶ X) (W : X.Opens) (a : Γ(X, ⊤)) :
    (h.app W).hom (resTop W a) = resTop _ (h.appTop.hom a) := by
  simp only [resTop, Scheme.Hom.appTop]
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

private theorem presheaf_map_resTop_eq_resTop {W W' : X.Opens} (h : W' ≤ W) (c : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := by
  simp only [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_comb {W W' : X.Opens} (hW : W' ≤ W) {I : Type} [Fintype I] (a : I → Γ(X, ⊤)) (y : I → Γ(X, W))
    (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (X.presheaf.map (homOfLE hW).op).hom x = ∑ l, resTop W' (a l) * (X.presheaf.map (homOfLE hW).op).hom (y l) := by
  subst hx

  simp only [map_sum, map_mul, presheaf_map_resTop_eq_resTop]

theorem pull_comb (h : Y ⟶ X) {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ h ⁻¹ᵁ W) {I : Type} [Fintype I]
    (a : I → Γ(X, ⊤)) (y : I → Γ(X, W)) (x : Γ(X, W)) (hx : x = ∑ l, resTop W (a l) * y l) :
    (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom x) =
      ∑ l, resTop W' (h.appTop.hom (a l)) * (Y.presheaf.map (homOfLE hW).op).hom ((h.app W).hom (y l)) := by
  subst hx

  simp only [map_sum, map_mul, app_resTop, presheaf_map_resTop_eq_resTop]

private theorem sum_mul_sum_eq_sum_reindex_sigma {M : Type} [CommRing M] {I : Type} [Fintype I] {m : I → ℕ} {N : ℕ}
    (e : Fin N ≃ Σ l, Fin (m l)) (A : I → M) (C P : ∀ l, Fin (m l) → M) (C' : Fin N → M)
    (hC : ∀ i, C' i = A (e i).1 * C (e i).1 (e i).2) :
    ∑ l, A l * ∑ i, C l i * P l i = ∑ i, C' i * P (e i).1 (e i).2 := by
  rw [Fintype.sum_equiv e (fun i => C' i * P (e i).1 (e i).2) (fun x => A x.1 * C x.1 x.2 * P x.1 x.2)
    (fun i => by rw [hC]), Fintype.sum_sigma]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

theorem secLin_comb (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y)
    {I : Type} [Fintype I] (a : I → Γ(Y', ⊤)) (s : I → LB.Sec (LB.LinComb L φ₁ ε₁))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (h₀ : ∀ j, s₀.f j = ∑ l, resTop _ (a l) * (s l).f j)
    {m : I → ℕ} (σ : ∀ l, Fin (m l) → LB.Sec (LB.LinComb L φ₂ ε₂)) (c : ∀ l, Fin (m l) → Γ(Y', ⊤))
    (H : ∀ l, GeneratorPullback.SecLin L φ₁ ε₁ (s l) φ₂ ε₂ (σ l) h (c l)) {N : ℕ} (e : Fin N ≃ Σ l, Fin (m l))
    (c' : Fin N → Γ(Y', ⊤)) (hc' : ∀ i, c' i = a (e i).1 * c (e i).1 (e i).2) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₀ φ₂ ε₂ (fun i => σ (e i).1 (e i).2) h c' := by
  intro j₁ j₂ hc
  rw [res_comb (W := L.wchart φ₁ j₁) _ a (fun l => (s l).f j₁) (s₀.f j₁) (h₀ j₁)]
  have H' := fun l => H l j₁ j₂ hc
  simp only [H']
  exact sum_mul_sum_eq_sum_reindex_sigma e _ _ _ _ (fun i => by rw [hc', resTop_mul])

theorem isoRelM_comb {X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁) (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (e₁ : h₁ ≫ g₁ = m ≫ f₁) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {I : Type} [Fintype I]
    (a : I → LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b : I → LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (α : I → Γ(Z₁, ⊤)) (β : I → Γ(Z₂, ⊤)) (hαβ : ∀ l, h₁.appTop.hom (α l) = h₂.appTop.hom (β l))
    (a₀ : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (b₀ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ))))
    (ha : ∀ j, a₀.f j = ∑ l, resTop _ (α l) * (a l).f j)
    (hb : ∀ j, b₀.f j = ∑ l, resTop _ (β l) * (b l).f j)
    (H : ∀ l, GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (a l) g₂ h₂ (b l)) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ a₀ g₂ h₂ b₀ := by
  refine ⟨e₁, e₂, fun p j₁ j₂ hj₁ hj₂ => ?_⟩
  rw [pull_comb h₂ (W := L₂.wchart (fun _ => g₂) j₂) _ β (fun l => (b l).f j₂) (b₀.f j₂) (hb j₂),
    pull_comb h₁ (W := L₁.wchart (fun _ => g₁) j₁) _ α (fun l => (a l).f j₁) (a₀.f j₁) (ha j₁), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(H l).2.2 p j₁ j₂ hj₁ hj₂, ← hαβ l, mul_left_comm]

theorem scal_mul {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (a b : R) :
    scal p (a * b) = scal p a * scal p b := by
  simp only [scal, map_mul]

end General

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {I : Type} (S : Finset I) (s : I → Fam D F k) (α : D.X) (j) :
    ((∑ l ∈ S, s l).s α).f j = ∑ l ∈ S, ((s l).s α).f j := by
  classical
  refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
  · rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  · rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem genF_left_comp_fst_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_fst]

private theorem genF_left_comp_snd_TFK {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
  unfold UnifPre.genF
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem expandsF_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen → ∀ (n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (s : Fin n → Fam D.toPre F k) (t₀ : LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), (∀ l, U.ExpandsF F k w (t l) (s l)) → (∀ jj, t₀.f jj = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t l).f jj) → U.ExpandsF F k w t₀ (∑ l, c l • s l) := by
  intro R _ _ I D A G _ _ U F _ _ k w hw n c t s t₀ ht h0
  choose σ hσ using ht
  choose m cc σ₁ f hE hS hF using fun l => (hσ l).2
  have e₂ : 𝟙 _ ≫ UnifPre.gFK (G := G) F =
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) := by
    unfold UnifPre.gFK
    exact Category.id_comp _
  refine ⟨secComb (fun l => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c l)) σ, ?_, ?_⟩
  · exact isoRelM_comb A.L U.LG.L _ _ w _ k _ _ _ _ (genF_left_comp_snd_TFK U F) e₂ t σ
      (fun l => scal (fst (TFK (R := R) F) A.A).left (c l)) _
      (fun l => by rw [← genF_left_comp_fst_TFK U F]; rfl) t₀ _ h0 (fun _ => rfl) (fun l => (hσ l).1)
  · refine ⟨∑ l, m l, fun i => c (finSigmaFinEquiv.symm i).1 * cc _ (finSigmaFinEquiv.symm i).2,
      fun i => σ₁ _ (finSigmaFinEquiv.symm i).2, fun i => f _ (finSigmaFinEquiv.symm i).2,
      fun i e => hE _ _ e, ?_, fun α => ?_⟩
    · exact secLin_comb U.LG.L _ _ _ _ _ _ σ _ (fun _ => rfl) σ₁ _ hS finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)
    · refine secLin_comb D.toPre.P.L _ _ _ _ _
        (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l)) (fun l => (s l).s α) _
        (fun j => by rw [fam_sum_f]; rfl) (fun l i => f l i α) _ (fun l => hF l α) finSigmaFinEquiv.symm _
        (fun i => scal_mul _ _ _)

end GlobalTheory.ExpansionLinear
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNu

theorem isUnit_of_generates {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {k : ℕ} {α : D.toPre.X} {s t : D.toPre.SecB k α} (hs : SecBGenerates k α s) {a : R}
    (h : SecIsMul D.toPre.P.A.hom a s t) : IsUnit a := by
  obtain ⟨b, hb, -⟩ := hs t
  have h₁ : SecIsMul D.toPre.P.A.hom 1 s s := fun j => by simp only [scal, resTop, map_one, _root_.one_mul]
  have h₂ : SecIsMul D.toPre.P.A.hom (a * b) s s := fun j => by
    conv_lhs => rw [h j, hb j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  exact IsUnit.of_mul_eq_one b ((hs s).unique h₂ h₁)

end GlobalTheory.ThetaNu
end
end

section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

private theorem relDim_eq_of_smoothOfRelativeDimension_grp {X Y : Scheme.{0}} (f : X ⟶ Y) (n m : ℕ) (x : X)
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hQ⟩ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  have hp := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra! H
    exact hp.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 H))
  have : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : algebraMap Γ(X, V) (Localization.Away t) 1 = 0 := Subsingleton.elim _ _
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at h0
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := h0
    have hc' : t ^ k = 0 := by simpa using hc
    exact htp (hp.mem_of_pow_mem k (by rw [hc']; exact Ideal.zero_mem _))
  have hn' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    (Localization.Away t) t _ h
  have hm' := hQ t ht
  let := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) (Localization.Away t) := hn'
  have a1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have : Algebra.IsStandardSmoothOfRelativeDimension m Γ(Y, U) (Localization.Away t) := hm'
  have a2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast a1.symm.trans a2

private theorem exists_limit_fan_smooth_relDim_mul {S : Scheme.{0}} (A : Over S) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom) :
    ∀ k : ℕ, ∃ c : Fan (fun _ : Fin k => A), Nonempty (IsLimit c) ∧
      SmoothOfRelativeDimension (k * g) c.pt.hom := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fan.mk (𝟙_ (Over S)) (fun i => Fin.elim0 i), ⟨Fan.IsLimit.mk _
      (fun s => CartesianMonoidalCategory.toUnit s.pt) (fun _ i => Fin.elim0 i)
      (fun _ _ _ => CartesianMonoidalCategory.toUnit_unique _ _)⟩, ?_⟩
    rw [zero_mul]
    show SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ k ih =>
    obtain ⟨c, ⟨hc⟩, hsm⟩ := ih
    refine ⟨extendFan (f := fun _ : Fin (k + 1) => A) c
      (BinaryFan.mk (CartesianMonoidalCategory.fst A c.pt) (CartesianMonoidalCategory.snd A c.pt)),
      ⟨extendFanIsLimit (fun _ : Fin (k + 1) => A) hc
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct A c.pt)⟩, ?_⟩
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (k * g)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (k * g)
    have h1 : SmoothOfRelativeDimension (k * g) (pullback.fst A.hom c.pt.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback A.hom c.pt.hom).flip hsm
    have h2 := smoothOfRelativeDimension_comp (n := k * g) (m := g) (pullback.fst A.hom c.pt.hom) A.hom
    rw [Nat.succ_mul]
    exact h2

theorem rank_and_g_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j), D'.rank = j * D.rank ∧ D'.P.g = j * D.P.g := by
  intro R _ _ j D D' pD
  rcases pD with ⟨pw, w, wg, wr, xe, cpr, wpsi⟩
  refine ⟨?_, ?_⟩
  · have e : D'.X ≃ₗ[ℤ] (Fin j → D.X) := xe.toIntLinearEquiv
    unfold DegPre.rank
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rcases pw with ⟨pr, hom, lim⟩
    obtain ⟨c, ⟨hc⟩, hsm⟩ := exists_limit_fan_smooth_relDim_mul D.P.A D.P.g D.P.5 j
    let e := IsLimit.conePointUniqueUpToIso lim hc
    have hw : e.hom.left ≫ c.pt.hom = D'.P.A.hom := Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := j * D.P.g) e.hom.left c.pt.hom
    rw [hw, zero_add] at h3
    let := D'.P.2
    have p : (𝟙_ (Over (Spec (CommRingCat.of R)))).left := (inferInstance : Nonempty (PrimeSpectrum R)).some
    exact relDim_eq_of_smoothOfRelativeDimension_grp D'.P.A.hom _ _ ((η[D'.P.A]).left p) D'.P.5 h3

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowGrp

theorem nonempty_torusExtension_of_isPowGrp : ∀ (K : Type) [Field K] (G' G : Over (Spec (CommRingCat.of K))) [GrpObj G'] [GrpObj G] (j : ℕ), IsPowGrp G' G j → Nonempty (TorusExtension G) → Nonempty (TorusExtension G') := by
  intro K _ G' G _ _ j p hT
  obtain ⟨T⟩ := hT
  cases T with
  | mk X B hB q hqm0 hqf0 hqs0 hqc0 i him0 hker =>
    have pB := ReciprocityTheory.ChartRestriction.G.Out.powIsPowGrp B j
    have pT := GlobalTheory.SplitTorusPow.isPowGrp (Spec (CommRingCat.of K)) (AddEquiv.refl (Fin j → X))
    obtain ⟨q', hq, hqm, hqf, hqs, hqc, -⟩ := GlobalTheory.PowMap.main _ G' G _ B j p pB q
    obtain ⟨i', hi, him, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p i
    exact ⟨{ X := Fin j → X
             addCommGroup := inferInstance
             free := inferInstance
             finite := inferInstance
             B := ReciprocityTheory.ChartRestriction.G.Out.powObj B j
             grpB := inferInstance
             isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j pB).2.2.2.1 hB
             q := q'
             q_hom := hqm hqm0
             q_flat := hqf hqf0
             q_surjective := hqs hqs0
             q_quasiCompact := hqc hqc0
             i := i'
             i_hom := him him0
             isKernel := GlobalTheory.PowKernel.main _ _ _ G' G _ _ j pT p pB i q i' q' hi hq hker }⟩

theorem isSemiAbelian_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G' G _ _ _ _ j p' hG
  obtain ⟨_, hs, hsep, hqc, hgc, hf⟩ := hG
  have hpow := GlobalTheory.PowGrp.powers S G' G j p'
  have hqg := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p'
  refine ⟨inferInstance, hpow.1 hs, hpow.2.1 hsep, hqg.1 hqc, hqg.2 hs hgc, ?_⟩
  intro Ω _ _ x
  obtain ⟨px, -⟩ := GlobalTheory.isPowGrp_baseChange S _ x G' G j p'
  exact nonempty_torusExtension_of_isPowGrp Ω _ _ j px (hf Ω x)

end GlobalTheory.PowGrp
end
