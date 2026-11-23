module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle690
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem spMap_comp' {A B K : Type} [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eSec_hom' {S : Scheme.{0}} (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  simpa [eSec] using Over.w η[G]

theorem gs_appLE' {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (p : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ φ ⁻¹ᵁ U)
    (hp : r p ∈ V) (a : Γ(X, U)) : gs r p V ((φ.appLE U V e).hom a) = gs (r ≫ φ) p U a := by
  rw [← gs_pull r φ p U (e hp) a, ← gs_res r p e hp]
  rfl

theorem dualMap_alg {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) (a : B) :
    GlobalTheory.MBLow.dualMap h (algebraMap B _ a) = algebraMap K _ (h a) := by
  ext <;> simp [GlobalTheory.MBLow.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {B K : Type} [CommRing B] [CommRing K] (h : B →+* K) :
    GlobalTheory.MBLow.dualMap h DualNumber.eps = DualNumber.eps := by
  ext <;> simp [GlobalTheory.MBLow.dualMap]

theorem dual_decomp {A : Type} [CommRing A] (z : DualNumber A) :
    z = algebraMap A _ z.fst + algebraMap A _ z.snd * DualNumber.eps := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ringHom_dual_ext {A K : Type} [CommRing A] [CommRing K] (F G : DualNumber A →+* K)
    (h1 : ∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) (h2 : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine DFunLike.ext _ _ fun z => ?_
  rw [dual_decomp z, map_add (f := _), map_add (f := _), map_mul, map_mul, h1, h1, h2]

end GlobalTheory.KeyEven

namespace GlobalTheory.KeyEven

theorem keyPB_of_keyOn_comp : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K)
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G))
    (x : KeyIn B) (x' : KeyIn K) (hg : x.P.g = g) (hg' : x'.P.g = g),
    KeyOn f x G L σ (fun i => y (i.cast hg)) → KeyOn (h.comp f) x' G L σ (fun i => y (i.cast hg')) → KeyPB x' x h := by
  intro A B K _ _ _ f h G _ _ L σ g y x x' hg hg' H H'
  obtain ⟨φ, he, ψ, F, hpb, hψ, hrig, hsec, hF1, hF2, hv⟩ := H
  obtain ⟨φ', he', ψ', F', hpb', hψ', hrig', hsec', hF1', hF2', hv'⟩ := H'
  have hc : spMap (h.comp f) = spMap h ≫ spMap f := spMap_comp' f h
  obtain ⟨φ₁, h1, h2⟩ : ∃ φ₁ : x'.P.A.left ⟶ x.P.A.left, φ₁ ≫ φ = φ' ∧ φ₁ ≫ x.P.A.hom = x'.P.A.hom ≫ spMap h :=
    ⟨hpb.1.lift φ' (x'.P.A.hom ≫ spMap h) (by rw [hpb'.1.w, hc, Category.assoc]), hpb.1.lift_fst _ _ _,
      hpb.1.lift_snd _ _ _⟩
  subst h1
  have gp : IsGrpPullback x'.P.A x.P.A (spMap h) φ₁ := IsGrpPullback.cancel hpb (hpb'.congr hc rfl) h2
  have he₁ : eSec x'.P.A ≫ φ₁ = spMap h ≫ eSec x.P.A := by
    apply hpb.1.hom_ext
    · rw [Category.assoc, he', Category.assoc, he, hc, Category.assoc]
    · rw [Category.assoc, h2, ← Category.assoc, eSec_hom', Category.assoc, eSec_hom']
      rfl
  have hL := L.isLB
  have hx := x.P.isLB
  have hx' := x'.P.isLB
  have pψ := (isGen_iff ψ).1 hψ
  have pψ' := (isGen_iff ψ').1 hψ'
  obtain ⟨w, T⟩ := exists_cancel hL ψ ψ' pψ pψ' hx hx'
  have hg₁ : x'.P.g = x.P.g := hg'.trans hg.symm
  refine ⟨φ₁, he₁, w, hg₁, GlobalTheory.MBLow.dualMap h, gp, (isGen_iff w).2 (T.pgen_cancel hL pψ pψ'), ?_, ?_,
    dualMap_alg h, dualMap_eps h, ?_⟩
  ·
    have H := (maps_iff ψ _ (fun _ => eSec G) _ x.rig L.rig (spMap f) _ (rigPull_le φ (spMap f) he L.L)
      (fun _ => rfl)).1 hrig
    have H'' := (maps_iff ψ' _ (fun _ => eSec G) _ x'.rig L.rig (spMap (h.comp f)) _
      (rigPull_le (φ₁ ≫ φ) (spMap (h.comp f)) he' L.L) (fun _ => rfl)).1 hrig'
    rw [hc] at H''
    exact (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap h) _ (rigPull_le φ₁ (spMap h) he₁ x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel hL (fun _ => he₁) H H'')
  ·
    intro j i hle
    apply fn_ext
    intro p hp
    obtain ⟨c, hcp⟩ := exists_chart hL (φ (φ₁ p))
    have hk : φ₁ p ∈ x.P.L.U (j PUnit.unit) := hle hp
    have le₀ : (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) ≤ φ ⁻¹ᵁ L.L.U c := fun q hq => mem_pull.1 hq.1
    have m₀ : φ₁ p ∈ (L.L.pull φ).U (fun _ => c) ⊓ x.P.L.U (j PUnit.unit) := ⟨mem_pull.2 hcp, hk⟩
    have e₀ := congrArg (gs φ₁ p _) (hsec (fun _ => c) (j PUnit.unit) le₀)
    dsimp only at e₀
    rw [gs_appLE' φ φ₁ p _ _ le₀ m₀] at e₀
    erw [gs_mul φ₁ p _ m₀] at e₀
    erw [gs_unit φ₁ p _ m₀, gs_res φ₁ p _ m₀] at e₀
    have le₁ : ((L.L.pull (φ₁ ≫ φ)).U (fun _ => c)) ⊓ x'.P.L.U i ≤ (φ₁ ≫ φ) ⁻¹ᵁ L.L.U c :=
      fun q hq => mem_pull.1 hq.1
    have m₁ : (𝟙 x'.P.A.left) p ∈ (L.L.pull (φ₁ ≫ φ)).U (fun _ => c) ⊓ x'.P.L.U i := ⟨mem_pull.2 hcp, hp.2⟩
    have e₁ := congrArg (gs (𝟙 _) p _) (hsec' (fun _ => c) i le₁)
    dsimp only at e₁
    rw [gs_appLE' (φ₁ ≫ φ) (𝟙 _) p _ _ le₁ m₁] at e₁
    erw [gs_mul (𝟙 _) p _ m₁] at e₁
    erw [gs_unit (𝟙 _) p _ m₁, gs_res (𝟙 _) p _ m₁] at e₁
    rw [Category.id_comp] at e₁
    have tri := T (x'.P.A.left) (𝟙 _) p c (j PUnit.unit) i hcp hk hp.2
    rw [gs_appLE' φ₁ (𝟙 _) p _ _ hle hp, Category.id_comp]
    erw [gs_mul (𝟙 _) p _ hp]
    erw [gs_unit (𝟙 _) p _ hp, gs_res (𝟙 _) p _ hp]
    change gs φ₁ p _ _ = (gw w (𝟙 _) p (j PUnit.unit) i).val * _
    have e₂ : (gw ψ' (𝟙 _) p c i).val * gs (𝟙 _) p (x'.P.L.U i) (x'.th.f i) =
        (gw ψ φ₁ p c (j PUnit.unit)).val * gs φ₁ p (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) :=
      e₁.symm.trans e₀
    rw [tri, Category.id_comp, Units.val_mul, _root_.mul_assoc] at e₂
    exact ((Units.mul_right_inj _).1 e₂).symm
  ·
    intro i
    apply hpb.1.hom_ext
    · have a1 := hv (i.cast hg₁)
      have a2 := hv' i
      simp only at a1 a2
      rw [Category.assoc, a2, Category.assoc, a1, Fin.cast_cast, ← Category.assoc, ← spMap_comp']
      congr 2
      refine ringHom_dual_ext _ _ (fun a => ?_) ?_
      · simp only [RingHom.comp_apply, hF1, hF1', dualMap_alg]
      · simp only [RingHom.comp_apply, hF2, hF2', dualMap_eps]
    · rw [Category.assoc, h2, ← Category.assoc, Over.w (x'.v i), Category.assoc, Over.w (x.v _)]
      show spMap (algebraMap K (DualNumber K)) ≫ spMap h = spMap (GlobalTheory.MBLow.dualMap h) ≫ spMap (algebraMap B (DualNumber B))
      rw [← spMap_comp', ← spMap_comp']
      congr 1
      exact RingHom.ext fun a => (dualMap_alg h a).symm

end GlobalTheory.KeyEven
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc


open GlobalTheory.CechPic in
theorem lam_trait_fibre_eq_univ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  intro g n o _ ζ F T W _ _ fK G'' _ β κ hκ hκβ α₂ hα₂
  have hL := T.U.LG.isLB
  have hA := T.A.isLB
  have hP := F.univ.isLB
  have hLβ := pull_isLB hL (pullback.fst G''.hom (jK W) ≫ β)
  have hB₁ : (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))).IsLB :=
    LB.isLB_linComb hLβ _ _
  refine (cls_eq_iff hB₁ (pull_isLB hP α₂)).1 ?_
  have c₂ : cls _ hB₁ = lam (CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL))
      (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))
      (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')) := by
    rw [← cls_pull hL _ hLβ]; exact cls_cube_two hLβ _ _ hB₁
  have hext : CechPic.pull T.U.gen.hom.left (cls _ hA) =
      CechPic.pull (pullback.fst T.G.hom (jK T.V)) (cls _ hL) := by
    have := (cls_eq_iff (pull_isLB hA T.U.gen.hom.left) (pull_isLB hL (pullback.fst T.G.hom (jK T.V)))).2 T.U.ext
    rwa [cls_pull hA, cls_pull hL] at this
  have hΛ : lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A) = CechPic.pull T.α₂ (cls _ hP) := by
    have hl : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb hA _ _
    have := (cls_eq_iff hl (pull_isLB hP T.α₂)).2 T.lb
    rw [cls_pull hP] at this
    exact (cls_cube_two hA _ _ hl).symm.trans this
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e₁ : CechPic.pull (pullback.fst G''.hom (jK W) ≫ β) (cls _ hL) = CechPic.pull κ (cls _ hA) := by
    rw [← hκβ, pull_comp, pull_comp, ← hext, ← pull_comp T.U.gen.inv.left, hgi, pull_id]
  rw [c₂, e₁, lam_pull_of_isGrpPullback hκ, cls_pull hP]
  set Q := lift (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
    (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) with hQdef
  have e₃ : lam (cls _ hA) (pushHom hκ _ (fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')))
      (pushHom hκ _ (snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G''))) =
      CechPic.pull Q.left (lam (cls _ hA) (fst T.A.A T.A.A) (snd T.A.A T.A.A)) := by
    rw [pull_lam, lift_fst, lift_snd]
  have hQ : Q.left ≫ T.α₂ = α₂ := by
    refine GlobalTheory.UnifLamFibre.isSquare_unique (φ := κ ≫ T.α) ⟨?_, ?_⟩ hα₂
    · rw [Category.assoc, T.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
      show ((fst ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
    · rw [Category.assoc, T.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
      show ((snd ((Over.pullback (jK W)).obj G'') ((Over.pullback (jK W)).obj G'')).left ≫ κ) ≫ T.α = _
      rw [Category.assoc]
  rw [e₃, hΛ, ← pull_comp, hQ]

end GlobalTheory.Poinc
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem sum_embeddings_eq_sum_places {K : Type} [Field K] [NumberField K] (g : (K →+* ℂ) → ℝ)
    (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ, g σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * g w.embedding := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
      rw [this, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

theorem t_embedding_mk {K : Type} [Field K] (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (σ : K →+* ℂ) : t (InfinitePlace.mk σ).embedding = t σ := by
  rcases embedding_mk_eq σ with h | h
  · rw [h]
  · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
      RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
    rw [h, this, ht]

theorem minkowskiBound_eq_absNorm_mul {K : Type} [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I = ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      minkowskiBound K 1 := by
  unfold minkowskiBound
  rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_fractionalIdealLatticeBasis]
  simp [mul_assoc]

end GlobalTheory.CovHt

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem exists_elt_balanced : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧
      (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  intro K _ _ e t ht

  have hNpos : ∀ la : HeightOneSpectrum (𝓞 K), (0 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNone : ∀ la : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have h := hNpos la
    have : (1 : ℕ) ≤ Ideal.absNorm la.asIdeal := by exact_mod_cast h
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set S : ℝ := e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ) with hS
  set A : ℝ := ∑ la ∈ e.support, Real.log (Ideal.absNorm la.asIdeal : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun la _ => Real.log_nonneg (hNone la)
  set V0 : ℝ := (minkowskiBound K 1).toReal with hV0
  have hV0nn : 0 ≤ V0 := ENNReal.toReal_nonneg
  set c : ℝ := |Real.log V0| + A + 1 with hc
  refine ⟨c, fun τ => ?_⟩
  set m : HeightOneSpectrum (𝓞 K) → ℤ := fun la => ⌈(τ : ℝ) * e la⌉ with hm
  have hm0 : ∀ la, la ∉ e.support → m la = 0 := by
    intro la hla
    rw [Finsupp.notMem_support_iff] at hla
    simp [hm, hla]
  have hmfin : ∀ᶠ v in Filter.cofinite, m v = 0 := by
    rw [Filter.eventually_cofinite]
    refine e.support.finite_toSet.subset fun v hv => ?_
    by_contra h
    exact hv (hm0 v h)
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ v, GroundTheory.Global.primeIdealUnit v ^ m v with hI
  have hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = m v :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow m hmfin

  have hnorm : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ la ∈ e.support, (Ideal.absNorm la.asIdeal : ℝ) ^ m la := by
    rw [hI, GroundTheory.Global.coe_finprod_primeIdealUnit_zpow m hmfin,
      finprod_eq_prod_of_mulSupport_subset (s := e.support)]
    · rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun la _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    · intro v hv
      by_contra h
      exact hv (by simp [hm0 v h])
  have hnormle : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) ≤ Real.exp (τ * S + A) := by
    rw [hnorm]
    have hS' : S = ∑ la ∈ e.support, e la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := rfl
    rw [hS', hA, Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun la _ => by positivity) fun la _ => ?_
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hNpos la)]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((m la : ℤ) : ℝ) ≤ τ * e la + 1 := (Int.ceil_lt_add_one _).le
    have h2 := Real.log_nonneg (hNone la)
    nlinarith

  set g : InfinitePlace K → ℝ := fun w => (τ : ℝ) * (cost e t - t w.embedding) + c with hg
  set f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (g w), (Real.exp_pos _).le⟩ with hf
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * g w = τ * S + (Module.finrank ℚ K : ℝ) * c := by
    have h := sum_embeddings_eq_sum_places (K := K) (fun σ => (τ : ℝ) * (cost e t - t σ) + c)
      (fun σ => by simp only [ht])
    rw [show (∑ w : InfinitePlace K, (w.mult : ℝ) * g w) =
        ∑ w : InfinitePlace K, (w.mult : ℝ) * ((τ : ℝ) * (cost e t - t w.embedding) + c) from rfl, ← h]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, nsmul_eq_mul]
    have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by positivity
    have hcost : (Module.finrank ℚ K : ℝ) * cost e t = S + ∑ σ, t σ := by
      rw [cost, mul_div_cancel₀ _ hn0]
    rw [hcost]; ring
  have hprod : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
    rw [NNReal.coe_prod, ← hsum, Real.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [NNReal.coe_pow, Real.exp_nat_mul]
    rfl
  have hmink : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, minkowskiBound_eq_absNorm_mul]
    have h1 : minkowskiBound K 1 = ENNReal.ofReal V0 := (ENNReal.ofReal_toReal (minkowskiBound_lt_top K 1).ne).symm
    rw [h1, ← ENNReal.ofReal_mul (by
      rw [hnorm]; exact Finset.prod_nonneg fun la _ => by positivity)]
    refine lt_of_lt_of_le ?_ (le_mul_of_one_le_left zero_le' (by exact_mod_cast one_le_convexBodyLTFactor K))
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by rw [hprod]; positivity), hprod]
    have hV : V0 ≤ Real.exp |Real.log V0| := by
      rcases hV0nn.eq_or_lt with h | h
      · rw [← h]; positivity
      · calc V0 = Real.exp (Real.log V0) := (Real.exp_log h).symm
          _ ≤ Real.exp |Real.log V0| := Real.exp_le_exp.2 (le_abs_self _)
    calc ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) * V0
        ≤ Real.exp (τ * S + A) * Real.exp |Real.log V0| :=
          mul_le_mul hnormle hV hV0nn (Real.exp_pos _).le
      _ = Real.exp (τ * S + (A + |Real.log V0|)) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
          refine Real.exp_lt_exp.2 ?_
          have hc0 : 0 ≤ c := by positivity
          nlinarith
  obtain ⟨α, hαI, hα0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hmink
  refine ⟨α, hα0, fun la => ?_, fun σ => ?_⟩
  · have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0
    have hle := FractionalIdeal.count_mono K la hsp (FractionalIdeal.spanSingleton_le_iff_mem.2 hαI)
    rw [hcount, GroundTheory.Global.count_spanSingleton la hα0] at hle
    have hv : vLa la α = -WithZero.log (la.valuation K α) := rfl
    calc (τ : ℝ) * e la ≤ (m la : ℝ) := Int.le_ceil _
      _ ≤ (vLa la α : ℝ) := by rw [hv]; exact_mod_cast hle
  · have h := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h
    have hpos : 0 < ‖σ α‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hα0)
    have : Real.log ‖σ α‖ ≤ Real.log (f (InfinitePlace.mk σ) : ℝ) := Real.log_le_log hpos h.le
    rw [show ((f (InfinitePlace.mk σ)) : ℝ) = Real.exp (g (InfinitePlace.mk σ)) from rfl, Real.log_exp] at this
    rw [hg] at this
    simp only [t_embedding_mk t ht σ] at this
    exact this

end GlobalTheory.CovHt
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_jK_unitOn (w : Rˣ) (z : (TK R).left) :
    gm (toUnit (TK R)).left z ⊤ (unitOn w) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)) := by
  have e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R := by simp
  rw [e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]
  congr 1
  apply Units.ext
  have := congrArg (fun q => q.hom (w : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem tauCoord_mul_unit {Q : Data R} {a b : Q.X} {k : (FractionRing R)ˣ} (h : Q.TauCoord a b k) (w : Rˣ) :
    Q.TauCoord a b (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := by
  obtain ⟨u, hu, hv⟩ := h
  let ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ := unitOn w⁻¹
  refine ⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩
  · show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)
    rw [map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]
    exact mul_left_comm _ _ _
  · rw [hv z J hJ]
    have hm := hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left
    show _ = _ * gm _ z _ (res le_top ρ * u.s _)
    erw [MonoidHom.map_mul, gm_res _ z le_top hm]
    have e3 : gm (toUnit (TK R)).left z ⊤ ρ =
        (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹ := by
      rw [← gm_jK_unitOn, ← MonoidHom.map_inv]
      exact congrArg _ (MonoidHom.map_inv _ _)
    have e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) =
        unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := MonoidHom.map_mul _ _ _
    rw [e3, e4, MonoidHom.map_mul]
    have : val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _) := rfl
    rw [this, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut
end
end
