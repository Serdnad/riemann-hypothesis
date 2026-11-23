module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_cont {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ : E ≃ₐ[F] E) {ι : Type*} [Fintype ι] (b : ι → E) (c : ι → B → A)
    (hc : ∀ i, Continuous (c i)) (hs : ∀ y, e.symm y = ∑ i, b i ⊗ₜ[F] c i y)
    (hm : Continuous fun a : A => e (1 ⊗ₜ a)) : Continuous (galOf e σ) := by
  have h : ∀ y, galOf e σ y = ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := by
    intro y
    change e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e.symm y)) = _

    rw [hs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have h' : (galOf e σ : B → B) = fun y => ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := funext h
  rw [h']
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hm.comp (hc i))

private theorem galAd_cont (σ : E ≃ₐ[F] E) : Continuous (galAd σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (adeleTensorEquiv F E) σ (Module.finBasis F E) (coord (Module.finBasis F E))
    (continuous_coord _) (adeleTensorEquiv_symm_apply _) ?_
  have h : (fun a : 𝔸[F] => adeleTensorEquiv F E ((1 : E) ⊗ₜ a)) = adeleMap F E := by
    funext a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h]
  exact continuous_adeleMap

private theorem galInf_cont (σ : E ≃ₐ[F] E) : Continuous (galInf σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
    (Module.finBasis F E) (GroundTheory.Global.InfinitePlace.adeleCoord (Module.finBasis F E))
    (GroundTheory.Global.InfinitePlace.continuous_adeleCoord _) (fun y => ?_) ?_
  · rw [AlgEquiv.symm_apply_eq]
    exact (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord _ y).symm
  · have h : (fun a : InfiniteAdeleRing F =>
        GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ a)) =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) := by
      funext a
      rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    rw [h]
    exact GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap

private theorem galFin_mul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (y : CompletionsOver E v) :
    galFin σ v (algebraMap (v.adicCompletion F) (CompletionsOver E v) a * y) =
      algebraMap (v.adicCompletion F) (CompletionsOver E v) a * galFin σ v y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  rw [← tensorEquiv'_tmul_mul]
  change tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 ⊗ₜ a) * t)))) =
    _ * tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v t)))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← tensorEquiv'_tmul_mul, map_mul,
    Algebra.TensorProduct.map_tmul]
  simp

private theorem galFin_cont (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun a y => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact galFin_mul σ v a y }
  exact IsModuleTopology.continuous_of_linearMap L

private theorem mapGL_cont {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (n : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

end

theorem UpperTheory.adele_galois_action_continuous :
    Compat → RPE → GalCont := by
  intro _ _ F E _ _ _ _ _ σ n
  exact ⟨mapGL_cont n _ (galAd_cont σ), mapGL_cont n _ (galInf_cont σ),
    fun v => mapGL_cont n _ (galFin_cont σ v)⟩
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section


open Classical in
private def psi {K : Type} [Field K] (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

private theorem continuous_psi {K : Type} [Field K] (w : InfinitePlace K) : Continuous (psi w) := by
  unfold psi
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem posRealElem_eq {K : Type} [Field K] (w : InfinitePlace K) {ρ : ℝ} (hρ : 0 < ρ) :
    posRealElem w (ρ ^ w.mult) = psi w ρ := by
  unfold posRealElem psi
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem real_hom_unique {A : Type} [Field A] [TopologicalSpace A] [T2Space A] (f g : ℝ →+* A)
    (hf : Continuous f) (hg : Continuous g) : f = g := by
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact RingHom.ext (congrFun h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem posIdele_fst {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w = psi w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  exact posRealElem_eq w hρ

private theorem inf_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace E) :
    InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1) w =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E).1 w := by
  have hx : ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1 =
      (RingHom.pi fun v : InfinitePlace F => psi v) ρ := funext fun v => posIdele_fst ρ hρ v
  rw [hx, posIdele_fst]
  have hc : Continuous (((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
      (InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))).comp
        (RingHom.pi fun v : InfinitePlace F => psi v)) :=
    (continuous_apply w).comp (InfinitePlace.continuous_infiniteAdeleRingMap.comp
      (continuous_pi fun v => continuous_psi v))
  exact congrArg (fun f : ℝ →+* w.Completion => f ρ) (real_hom_unique _ (psi w) hc (continuous_psi w))

private theorem fin_posIdele {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 = 1 :=
  IsDedekindDomain.FiniteAdeleRing.ext K fun v => posIdele_finite ρ hρ v

private theorem adeleMap_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    AdeleBaseChange.adeleMap F E ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F) =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E) := by
  rw [AdeleBaseChange.adeleMap_apply]
  refine Prod.ext (funext fun w => inf_posIdele ρ hρ w) ?_
  change AdeleBaseChange.finiteAdeleMap F E _ = _
  rw [fin_posIdele, fin_posIdele, map_one]

private theorem exponent (n : ℕ) (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ (s ^ Module.finrank F E) =
      rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s := by
  refine Subtype.ext ?_
  change ((s ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ =
    (s : ℝ) ^ ((n * Module.finrank ℚ F : ℝ))⁻¹
  have hk : Module.finrank ℚ F * Module.finrank F E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hk0 : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le, ← hk]
  congr 1
  push_cast
  field_simp

theorem UpperTheory.centralSection_baseChange :
    CentBC := by
  intro F E _ _ _ _ _ n s
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hn : 0 < n := i.pos
  have h1 : centralSection E n (s ^ Module.finrank F E) =
      diagUnits n fun _ => posIdeleHom E (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, exponent n hn, scalarUnits_apply]
  have h2 : centralSection F n s =
      diagUnits n fun _ => posIdeleHom F (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply]
  rw [h1, h2, coe_diagUnits]
  change AdeleBaseChange.adeleMap F E (((diagUnits n fun _ => posIdeleHom F _ : AdelicGLn.AdelicGL F n)).val i j) = _
  rw [coe_diagUnits]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdeleHom_apply, posIdeleHom_apply]
    exact adeleMap_posIdele _ _
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
end
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Filter

namespace UpperTheory.ConvolutionTheory.T4.RPGroup

section
universe u
variable {W V : Type} {I : V → Type}

private theorem exists_fam (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    {X : W → Type u} (T : ∀ v (i : I v), X (ι v i)) :
    ∃ f : ∀ w, X w, ∀ v i, f (ι v i) = T v i := by
  have h : ∀ w, ∃ x : X w, ∀ v i (h : ι v i = w), h ▸ T v i = x := by
    intro w
    obtain ⟨v, i, rfl⟩ := hs w
    refine ⟨T v i, fun v' i' h => ?_⟩
    have hv : v' = v := by rw [← hb v' i', h, hb]
    subst hv
    have hi : i' = i := hinj v' h
    subst hi
    rfl
  choose f hf using h
  exact ⟨f, fun v i => (hf _ v i rfl).symm⟩

private theorem ev_up [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    {P : W → Prop} (h : ∀ᶠ w in cofinite, P w) : ∀ᶠ v in cofinite, ∀ i, P (ι v i) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image b).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  exact ⟨ι v i, hi, hb v i⟩

private theorem ev_down [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hs : ∀ w, ∃ v i, ι v i = w) {P : V → Prop} (h : ∀ᶠ v in cofinite, P v) :
    ∀ᶠ w in cofinite, P (b w) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.biUnion fun v _ => Set.finite_range (ι v)).subset fun w hw => ?_
  obtain ⟨v, i, rfl⟩ := hs w
  simp only [Set.mem_setOf_eq, hb] at hw
  exact Set.mem_biUnion hw ⟨i, rfl⟩

variable {G Gi : Type} {H : W → Type} {Gv : V → Type} [Group G] [Group Gi] [∀ w, Group (H w)]
  [∀ v, Group (Gv v)] [TopologicalSpace G] [TopologicalSpace Gi] [∀ w, TopologicalSpace (H w)]
  [∀ v, TopologicalSpace (Gv v)] [T2Space Gi] [∀ v, T2Space (Gv v)]

private theorem rp_group [∀ v, Finite (I v)] {q : G →* Gi} {p : ∀ w, G →* H w} {K : ∀ w, Subgroup (H w)}
    (hRP : RP q p K) (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    (e : ∀ v, Gv v ≃ₜ* ∀ i : I v, H (ι v i)) (p' : ∀ v, G →* Gv v) (K' : ∀ v, Subgroup (Gv v))
    (hp : ∀ v i g, e v (p' v g) i = p (ι v i) g)
    (hK : ∀ v x, x ∈ K' v ↔ ∀ i, e v x i ∈ K (ι v i)) : RP q p' K' := by
  have hcp : ∀ v, Continuous (p' v) := by
    intro v
    have h : ⇑(p' v) = fun g => (e v).symm (fun i => p (ι v i) g) := by
      funext g
      apply (e v).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact funext fun i => hp v i g
    rw [h]
    exact (e v).symm.continuous.comp (continuous_pi fun i => hRP.cp _)
  have hKset : ∀ v, (K' v : Set (Gv v)) = e v ⁻¹' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
    intro v
    ext x
    simp only [SetLike.mem_coe, hK, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine ⟨hRP.cq, hcp, fun v => ?_, fun v => ?_, fun g => ?_, fun S => ?_, fun g g' hq h => ?_,
    fun gi gv hgv => ?_, fun Ci C hCi hC hev => ?_⟩
  · rw [hKset]
    exact (isOpen_set_pi Set.finite_univ fun i _ => hRP.opn _).preimage (e v).continuous
  · have h : (K' v : Set (Gv v)) = (e v).symm '' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
      rw [hKset]
      ext x
      constructor
      · intro hx
        exact ⟨e v x, hx, (e v).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [Set.mem_preimage] using hy
    rw [h]
    exact (isCompact_univ_pi fun i => hRP.cpt _).image (e v).symm.continuous
  · refine (ev_up ι b hb (hRP.ae g)).mono fun v h => ?_
    rw [hK]
    intro i
    rw [hp]
    exact h i
  · have hfin : (⋃ v ∈ (S : Set V), Set.range (ι v)).Finite :=
      S.finite_toSet.biUnion fun v _ => Set.finite_range (ι v)
    have hmem : ∀ w, w ∈ hfin.toFinset ↔ b w ∈ S := by
      intro w
      rw [Set.Finite.mem_toFinset]
      constructor
      · intro h
        obtain ⟨v, hv, i, rfl⟩ := Set.mem_iUnion₂.1 h
        rw [hb]
        exact hv
      · intro h
        obtain ⟨v, i, rfl⟩ := hs w
        rw [hb] at h
        exact Set.mem_biUnion h ⟨i, rfl⟩
    have h : (US p' K' S : Set G) = US p K hfin.toFinset := by
      ext g
      simp only [SetLike.mem_coe, mem_US]
      constructor
      · intro h w hw
        obtain ⟨v, i, rfl⟩ := hs w
        have hv : v ∉ S := by
          rw [hmem, hb] at hw
          exact hw
        have := (hK v _).1 (h v hv) i
        rwa [hp] at this
      · intro h v hv
        rw [hK]
        intro i
        rw [hp]
        exact h _ (by rw [hmem, hb]; exact hv)
    rw [h]
    exact hRP.opnU _
  · refine hRP.ext g g' hq fun w => ?_
    obtain ⟨v, i, rfl⟩ := hs w
    rw [← hp, ← hp, h]
  · obtain ⟨gw, hgw⟩ := exists_fam ι b hb hinj hs (X := H) fun v i => e v (gv v) i
    have hae : ∀ᶠ w in cofinite, gw w ∈ K w := by
      refine (ev_down ι b hb hs hgv).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hgw]
      exact (hK v _).1 h i
    obtain ⟨g, hq, hpg⟩ := hRP.surj gi gw hae
    refine ⟨g, hq, fun v => (e v).injective (funext fun i => ?_)⟩
    rw [hp, hpg, hgw]
  · obtain ⟨D, hD⟩ := exists_fam ι b hb hinj hs (X := fun w => Set (H w))
      fun v i => (fun x => e v x i) '' C v
    have hDc : ∀ w, IsCompact (D w) := by
      intro w
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hD]
      exact (hC v).image ((continuous_apply i).comp (e v).continuous)
    have hDe : ∀ᶠ w in cofinite, D w ⊆ K w := by
      refine (ev_down ι b hb hs hev).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hD]
      rintro _ ⟨x, hx, rfl⟩
      exact (hK v x).1 (h hx) i
    have hA := hRP.prop Ci D hCi hDc hDe
    have hcl : IsClosed {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} := by
      have h : {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} = q ⁻¹' Ci ∩ ⋂ v, p' v ⁻¹' C v := by
        ext g
        simp
      rw [h]
      exact (hCi.isClosed.preimage hRP.cq).inter
        (isClosed_iInter fun v => (hC v).isClosed.preimage (hcp v))
    refine hA.of_isClosed_subset hcl ?_
    rintro g ⟨h1, h2⟩
    refine ⟨h1, fun w => ?_⟩
    obtain ⟨v, i, rfl⟩ := hs w
    rw [hD, ← hp]
    exact ⟨_, h2 v, rfl⟩

end

end UpperTheory.ConvolutionTheory.T4.RPGroup

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic in
theorem UpperTheory.restrictedProduct_extension_of_base_regroup :
    RPF → RPE := by
  intro hF F E _ _ _ _ _ n
  refine UpperTheory.ConvolutionTheory.T4.RPGroup.rp_group (I := fun v : Pl F => PlacesOver E v) (hF E n)
    (fun v i => i.1) (below F) (fun v i => (below_eq_iff i.1 v).2 i.2)
    (fun v => Subtype.val_injective)
    (fun w => ⟨below F w, ⟨w, (below_eq_iff w _).1 rfl⟩, rfl⟩)
    (fun v => glPiEquiv (Fin n) fun w : PlacesOver E v => w.1.adicCompletion E)
    (fun v => pE E n v) (fun v => KE E n v) ?_ ?_
  · intro v i g
    refine Units.ext ?_
    ext a b
    rfl
  · intro v x
    have h : ∀ w : PlacesOver E v,
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) x =
          glPiEquiv (Fin n) (fun w : PlacesOver E v => w.1.adicCompletion E) x w := by
      intro w
      refine Units.ext ?_
      ext a b
      rfl
    change (∀ w : PlacesOver E v, _ ∈ _) ↔ _
    exact forall_congr' fun w => by rw [h w]
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.separableLocal_of_separableScalar :
    SepSc → CentLoc → SepLoc := by
  intro hS hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hI : ((pI F n (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (InfiniteAdeleRing F)) := by
    ext a b
    rfl
  have hIs : (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable := by
    rw [hI, Matrix.charpoly_map]
    exact hsep.map
  refine ⟨hIs, fun s => ?_, fun v => ?_⟩
  · obtain ⟨⟨r, hr⟩, -⟩ := hC F n ⟨Real.exp s, Real.exp_pos s⟩
    have h := hr (pI F n (AdelicGLn.diagonal F n γ))
    have h' : (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val =
        (r : InfiniteAdeleRing F) • (pI F n (AdelicGLn.diagonal F n γ)).val := h
    rw [h']
    exact hS _ n r _ hIs
  · have hv : ((finAt v (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) := by
      ext a b
      rfl
    rw [hv, Matrix.charpoly_map]
    exact hsep.map
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.haar_quotient_subgroup :
    QSub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨ρ₀, -, hρ₀, -⟩ := normEx H T μ j ν hp
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  have hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ := by
    refine ⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0,
      hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩
    have e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G))
        = (ρ₀ (j t * x) : ENNReal) := fun t => by
      rw [← Subgroup.coe_mul]
      exact hinj.extend_apply _ _ _
    simp only [e]
    exact hρ₀.2 x
  unfold quotInt
  rw [dite_eq_left hex]
  have hn : IsNrm j ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by
      simpa only [Subgroup.coe_mul] using hex.choose_spec.2 x⟩
  exact ((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm
end
