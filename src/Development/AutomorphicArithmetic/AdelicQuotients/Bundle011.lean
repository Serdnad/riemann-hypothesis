module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.Bundle001
import GroundTheory.GlobalFields.Adele.Topology
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc

private theorem cenClosed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | g * x = x * g} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem cenLC {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (g : G) : LocallyCompactSpace (Subgroup.centralizer {g} : Subgroup G) :=
  (cenClosed g).isClosedEmbedding_subtypeVal.locallyCompactSpace

private theorem diag_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (δ : GL (Fin n) E) :
    detModule E n (AdelicGLn.diagonal E n δ) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨δ, rfl⟩)

theorem UpperTheory.globalOrbitalComparison_of_split :
    QSub → SplitQ → UniOf → TComm → Spl → N3 → N5 → CentBC → Glob := by
  intro hQ hS hU hT hSpl hN3 hN5 _ F E _ _ _ _ _ _ σ hσ n hn μE μF hE hF
  obtain ⟨⟨eE, heE⟩, hG⟩ := hSpl F E σ hσ n hn
  let l : Measure {r : ℝ // 0 < r} := Measure.haar
  have hl : Uni l := (hU _ l inferInstance).2 mul_comm
  have hUE : Uni μE := (hU _ μE hE).1 inferInstance
  have hUF : Uni μF := (hU _ μF hF).1 inferInstance
  let eF : G1 F n × {r : ℝ // 0 < r} ≃ₜ* GA F n := (glNormOneSplitting (K := F) hn).symm
  refine ⟨(μE.prod l).map eE, (μF.prod l).map eF, ?_, ?_, ?_⟩
  · exact (hS (G1 E n) (G1 E n) _ (GA E n) (GA E n) μE (MonoidHom.id _) μE l
      ⟨hUE, Topology.IsClosedEmbedding.id, hUE⟩ hl eE eE (MonoidHom.id _) (fun _ => rfl)).1.1
  · exact (hS (G1 F n) (G1 F n) _ (GA F n) (GA F n) μF (MonoidHom.id _) μF l
      ⟨hUF, Topology.IsClosedEmbedding.id, hUF⟩ hl eF eF (MonoidHom.id _) (fun _ => rfl)).1.1
  intro γ γ₁ hγ hreg ν hν
  obtain ⟨⟨eT, heT⟩, j, hj, hjv⟩ := hG γ γ₁ hγ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) := cenLC γ₁
  haveI : SecondCountableTopology (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (TA γ) := cenLC _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hUν : Uni ν := (hU _ ν hν).2 ((hT F n γ hreg).2.2.2 γ₁ hγ)
  have hPF : Pair μF (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν :=
    ⟨hUF, (cenClosed γ₁).isClosedEmbedding_subtypeVal, hUν⟩
  have sF := hS (G1 F n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA F n) (TA γ) μF
    (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν l hPF hl eF eT (TA γ).subtype
    (fun x => heT x)
  have hPE : Pair μE j ν := ⟨hUE, hj, hUν⟩
  have sE := hS (G1 E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA E n) (TA γ) μE j ν l hPE hl eE eT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype)
    (fun x => by
      rw [heE, MonoidHom.comp_apply, Subgroup.subtype_apply, heT, map_mul, hjv])
  refine ⟨(ν.prod l).map eT, sF.1.2.2.1, ?_, ?_⟩
  · intro Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA F n), FF γ Φ ((TA γ).subtype t * g) = FF γ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have hc : ((t : GA F n) * g)⁻¹ * AdelicGLn.diagonal F n γ * ((t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal F n γ * g := by
        rw [_root_.mul_inv_rev, mul_assoc g⁻¹, mul_assoc g⁻¹, mul_assoc, ← mul_assoc _ (t : GA F n) g, ← ht]
        group
      simp only [FF, Subgroup.subtype_apply, hc]
    rw [← (sF.2 (FF γ Φ) hΦ inv)]
    have hx : (fun x : G1 F n => FF γ Φ (eF (x, 1))) = fun x => avg Φ (x⁻¹ * γ₁ * x) := by
      funext x
      have h1 : eF (x, 1) = (x : GA F n) := by
        change (x : GA F n) * centralSection F n 1 = x
        rw [map_one, mul_one]
      rw [h1]
      simp only [FF, avg, Subgroup.coe_mul, Subgroup.coe_inv, hγ]
    rw [hx]
    rfl
  · intro δ hδ Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA E n),
        FE σ δ Φ (((mapGL n (adeleMap F E)).comp (TA γ).subtype) t * g) = FE σ δ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have h3 := (hN3 F E σ hσ n hn δ γ hreg hδ (mapGL n (adeleMap F E) (t : GA F n))).2 ⟨t, ht, rfl⟩
      have hc : (mapGL n (adeleMap F E) (t : GA F n) * g)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) g := by
        rw [map_mul, _root_.mul_inv_rev]
        calc _ = g⁻¹ * ((mapGL n (adeleMap F E) (t : GA F n))⁻¹ * AdelicGLn.diagonal E n δ *
              mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n))) * mapGL n (galAd σ) g := by group
          _ = _ := by rw [h3]
      simp only [FE, MonoidHom.comp_apply, Subgroup.subtype_apply, hc]
    rw [← (sE.2 (FE σ δ Φ) hΦ inv)]
    have h1 : ∀ x : G1 E n, eE (x, 1) = (x : GA E n) := by
      intro x
      rw [heE]
      simp only [map_one, mul_one]
    have hm : ∀ x : G1 E n, (x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n) ∈
        normOneGL (K := E) (n := n) := by
      intro x
      have hx : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, (hN5 F E σ hσ n hn).2.2, hx, diag_mem]
      simp
    have hx : (fun x : G1 E n => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ *
        mapGL n (galAd σ) (x : GA E n))) = fun x => FE σ δ Φ (eE (x, 1)) := by
      funext x
      rw [h1, ext0, dite_eq_left (hm x)]
      rfl
    rw [hx]
    have hmeas : Measurable fun x : G1 E n => FE σ δ Φ (eE (x, 1)) := by
      simp only [h1]
      exact hΦ.comp measurable_subtype_coe
    have hinv : ∀ (t : Subgroup.centralizer {γ₁}) (g : G1 E n),
        FE σ δ Φ (eE (j t * g, 1)) = FE σ δ Φ (eE (g, 1)) := by
      intro t g
      have h2 := inv (eT (t, 1)) (g : GA E n)
      have h4 : ((mapGL n (adeleMap F E)).comp (TA γ).subtype) (eT (t, 1)) = (j t : GA E n) := by
        rw [MonoidHom.comp_apply, Subgroup.subtype_apply, heT, hjv]
        simp only [map_one, mul_one]
      rw [h4] at h2
      rw [h1, h1]
      simpa using h2
    have hq := hQ (GA E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) (normOneGL (K := E) (n := n)) isClosed_normOneGL
      μE j ν hPE _ hmeas hinv
    have hj' : (fun t : Subgroup.centralizer {γ₁} => (j t : GA E n)) =
        fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) := funext hjv
    rw [hj'] at hq
    exact hq
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Core Topology GroundTheory.Global.AdeleBaseChange

private theorem mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) (t : Subgroup.centralizer {γ₁}) :
    ((t : G1 K n) : GA K n) ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← h]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 t.2)

private noncomputable def cenIn {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) : Subgroup.centralizer {γ₁} →* TA γ where
  toFun t := ⟨((t : G1 K n) : GA K n), mem_TA h t⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem cs_mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : GL (Fin n) K)
    (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact centralSection_mul_comm s _

private theorem isClosed_cen {K : Type} [Field K] [NumberField K] {n : ℕ} (γ₁ : G1 K n) :
    IsClosed (Subgroup.centralizer {γ₁} : Set (G1 K n)) := by
  have : (Subgroup.centralizer {γ₁} : Set (G1 K n)) = {x | x * γ₁ = γ₁ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem UpperTheory.splitCentralizer_of_splitEquiv :
    SplitEquiv → N5 → CentBC → Spl := by
  intro hS hN hC F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hcl, hmod, -⟩ := hN F E σ hσ n hn
  have hl : 0 < Module.finrank F E := Module.finrank_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hS (G1 E n) {r : ℝ // 0 < r} (GA E n) (normOneGL (K := E) (n := n)).subtype
      ((rpowHom ((Module.finrank F E : ℝ))⁻¹).comp (detModule E n))
      ((mapGL n (adeleMap F E)).comp (centralSection F n))
      IsEmbedding.subtypeVal
      ((continuous_rpowHom _).comp continuous_detModule)
      (hcl.continuous.comp continuous_centralSection)
      (fun s => by
        refine Subtype.ext ?_
        change ((detModule E n (mapGL n (adeleMap F E) (centralSection F n s)) : ℝ)) ^
          ((Module.finrank F E : ℝ))⁻¹ = s.1
        rw [hmod, detModule_centralSection hn]
        exact Real.pow_rpow_inv_natCast s.2.le hl.ne')
      (fun s g => by
        change mapGL n (adeleMap F E) (centralSection F n s) * g = g * mapGL n (adeleMap F E) (centralSection F n s)
        rw [hC F E n s]
        exact centralSection_mul_comm _ g)
      (fun g => by
        constructor
        · intro hg
          have h1 : ((detModule E n g : ℝ)) ^ ((Module.finrank F E : ℝ))⁻¹ = 1 := congrArg Subtype.val hg
          have h2 : (detModule E n g : ℝ) = 1 := by
            have h3 := Real.rpow_inv_natCast_pow (detModule E n g).2.le hl.ne'
            rw [h1, one_pow] at h3
            exact h3.symm
          exact ⟨⟨g, mem_normOneGL_iff_detModule.2 (Subtype.ext h2)⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          have h1 : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
          change rpowHom _ (detModule E n (x : GA E n)) = 1
          rw [h1, map_one])
    exact ⟨e, he⟩
  · intro γ γ₁ h
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hS (Subgroup.centralizer {γ₁}) {r : ℝ // 0 < r} (TA γ) (cenIn h)
        ((detModule F n).comp (TA γ).subtype)
        ((centralSection F n).codRestrict (TA γ) (cs_mem_TA γ))
        ((IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : TA γ → GA F n))).1
          (show IsEmbedding ((Subtype.val : G1 F n → GA F n) ∘ (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n)) from
            IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal))
        (continuous_detModule.comp continuous_subtype_val)
        (continuous_centralSection.subtype_mk _)
        (fun s => detModule_centralSection hn s)
        (fun s g => Subtype.ext (centralSection_mul_comm s _))
        (fun g => by
          constructor
          · intro hg
            have h1 : (g : GA F n) ∈ normOneGL (K := F) (n := n) := mem_normOneGL_iff_detModule.2 hg
            refine ⟨⟨⟨g, h1⟩, ?_⟩, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            refine Subtype.ext ?_
            change (g : GA F n) * (γ₁ : GA F n) = (γ₁ : GA F n) * g
            rw [h]
            exact Subgroup.mem_centralizer_singleton_iff.1 g.2
          · rintro ⟨x, rfl⟩
            exact mem_normOneGL_iff_detModule.1 x.1.2)
      exact ⟨e, fun x => congrArg Subtype.val (he x)⟩
    · have hmem : ∀ t : Subgroup.centralizer {γ₁},
          mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) ∈ normOneGL (K := E) (n := n) := fun t => by
        refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
        rw [hmod, mem_normOneGL_iff_detModule.1 (t : G1 F n).2]
        simp
      let j : Subgroup.centralizer {γ₁} →* G1 E n :=
        { toFun := fun t => ⟨mapGL n (adeleMap F E) ((t : G1 F n) : GA F n), hmem t⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine ⟨j, ?_, fun t => rfl⟩
      have hE : IsClosedEmbedding (Subtype.val : G1 E n → GA E n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hF : IsClosedEmbedding (Subtype.val : G1 F n → GA F n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hT : IsClosedEmbedding (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n) :=
        (isClosed_cen γ₁).isClosedEmbedding_subtypeVal
      exact (IsClosedEmbedding.of_comp_iff hE).1 (hcl.comp (hF.comp hT))
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace UpperTheory.Bnd

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

private def emb : GL (Fin n) (InfiniteAdeleRing E) →* GA E n where
  toFun x := (AdelicGLn.prodEquiv E n).symm (x, 1)
  map_one' := map_one (AdelicGLn.prodEquiv E n).symm
  map_mul' x y := by
    rw [← map_mul (AdelicGLn.prodEquiv E n).symm]
    simp

private theorem emb_apply (x : GL (Fin n) (InfiniteAdeleRing E)) :
    emb E n x = (AdelicGLn.prodEquiv E n).symm (x, 1) := rfl

private theorem continuous_emb : Continuous (emb E n) :=
  (AdelicGLn.prodEquiv E n).symm.continuous.comp (continuous_id.prodMk continuous_const)

private theorem prod_emb (x : GL (Fin n) (InfiniteAdeleRing E)) :
    AdelicGLn.prodEquiv E n (emb E n x) = (x, 1) := by
  rw [emb_apply]; exact (AdelicGLn.prodEquiv E n).apply_symm_apply _

private theorem pI_emb (x : GL (Fin n) (InfiniteAdeleRing E)) : pI E n (emb E n x) = x := by
  refine Units.ext ?_
  ext a b
  have h := AdelicGLn.prodEquiv_apply_fst E n (emb E n x) a b
  rw [prod_emb] at h
  exact h.symm

private theorem pE_emb {F : Type} [Field F] [NumberField F] [Algebra F E] (v : Pl F)
    (x : GL (Fin n) (InfiniteAdeleRing E)) : pE E n v (emb E n x) = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h := AdelicGLn.prodEquiv_apply_snd E n (emb E n x) a b
  rw [prod_emb] at h
  change (((emb E n x : GL _ _) a b).2 : FiniteAdeleRing (𝓞 E) E) w.1 = _
  rw [← h]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

end UpperTheory.Bnd

open UpperTheory.Bnd in
theorem UpperTheory.adelicBound_of_centralizer_localization :
    N5 → Compat → CentLoc → RPE → BoundE := by
  intro hN hC hCL hR F E _ _ _ _ _ _ σ hσ n hn δ D hD
  have hRP := hR F E n
  obtain ⟨hC1, hC2, -⟩ := hC F E σ n

  have hz : ∀ s : ℝ, emb E n (pI E n (zA E n s)) = zA E n s := fun s =>
    hRP.ext _ _ (pI_emb E n _) fun v => by
      rw [pE_emb E n v]
      exact ((hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v).symm

  have hg : ∀ x, emb E n (mapGL n (galInf σ) x) = mapGL n (galAd σ) (emb E n x) := fun x =>
    hRP.ext _ _ (by rw [pI_emb, hC1, pI_emb]) fun v => by
      rw [pE_emb E n v, hC2, pE_emb E n v, map_one]
  have hm := (hN F E σ hσ n hn).2.2
  set d : GL (Fin n) (InfiniteAdeleRing E) →* {r : ℝ // 0 < r} := (detModule E n).comp (emb E n) with hd
  have hdc : Continuous fun y => (d y : ℝ) :=
    continuous_subtype_val.comp (continuous_detModule.comp (continuous_emb E n))
  have hdz : ∀ s : ℝ, (d (pI E n (zA E n s)) : ℝ) = Real.exp s := fun s => by
    simp only [hd, MonoidHom.comp_apply, hz]
    rw [zA, detModule_centralSection hn]
  have hds : ∀ x, d (mapGL n (galInf σ) x) = d x := fun x => by
    simp only [hd, MonoidHom.comp_apply, hg, hm]
  have hp : ∀ y, (d y : ℝ) ≠ 0 := fun y => (d y).2.ne'
  have hcont : Continuous fun y => Real.log ((d y : ℝ) / (d δ : ℝ)) :=
    (hdc.div_const _).log fun y => div_ne_zero (hp y) (hp δ)
  refine ⟨(fun y => Real.log ((d y : ℝ) / (d δ : ℝ))) '' D, hD.image hcont, fun s x hx => ⟨_, hx, ?_⟩⟩
  have e : d (pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x)) = d (pI E n (zA E n s)) * d δ := by
    rw [map_mul, map_mul, map_mul, hds, map_inv]
    congr 1
    rw [mul_comm (d x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  change Real.log ((d _ : ℝ) / (d δ : ℝ)) = s
  rw [e, Positive.val_mul, hdz, mul_div_cancel_right₀ _ (hp δ), Real.log_exp]
end
end

section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic :
    N1 → N2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ δ : GL (Fin n) E, EllElt σ δ →
        ∃ γ : GL (Fin n) F, Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly ∧
          ∀ γ' : GL (Fin n) F, (γ' : Matrix (Fin n) (Fin n) F).charpoly = (γ : Matrix (Fin n) (Fin n) F).charpoly →
            (∃ δ' : GL (Fin n) E, normGL σ δ' = incl γ') ∧
            ∀ δ' : GL (Fin n) E, normGL σ δ' = incl γ' → ∃ h : GL (Fin n) E, δ = h⁻¹ * δ' * sigmaGL σ h := by
  intro hN1 hN2 F E _ _ _ _ _ _ σ hgen n _ δ hδ
  obtain ⟨p, hp, hpm⟩ := hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hc : ∀ d h : GL (Fin n) E, normGL σ (h⁻¹ * d * sigmaGL σ h) = h⁻¹ * normGL σ d * h :=
    fun d h => twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h d
  have hreg : IsTwRegSemisimple σ δ := by
    unfold IsTwRegSemisimple
    rw [← hpm]
    exact hp.separable.map
  obtain ⟨h, γ, hγ⟩ := hN1 F E σ hgen n δ hreg
  have hv : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := rfl
  have hγp : (γ : Matrix (Fin n) (Fin n) F).charpoly = p := by
    apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    rw [hpm, ← Matrix.charpoly_map, ← hv, ← hγ, hc, Units.val_mul, Units.val_mul,
      Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  refine ⟨γ, hγp ▸ hp, fun γ' hγ' => ?_⟩
  have hr : IsRegSemisimple γ := by
    unfold IsRegSemisimple
    rw [hγp]; exact hp.separable
  have hr' : IsRegSemisimple γ' := by
    unfold IsRegSemisimple
    rw [hγ', hγp]; exact hp.separable
  obtain ⟨g, hg⟩ := (hN2 F E σ hgen n).2 γ γ' hr hγ'.symm
  have h0 : normGL σ ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) = incl γ' := by
    rw [hc, hγ, hg, map_mul, map_mul, map_inv]
  refine ⟨⟨_, h0⟩, fun δ' hδ' => ?_⟩
  obtain ⟨k, hk⟩ := (hN2 F E σ hgen n).1 δ' _ γ' hr' hδ' h0
  refine ⟨k * (incl g)⁻¹ * h⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv]
  calc δ = h * incl g * ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) *
        (sigmaGL σ (incl g))⁻¹ * (sigmaGL σ h)⁻¹ := by group
    _ = _ := by rw [hk]; group
end

section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_closedEmbedding_normOneAdelicGL_baseChange :
    N5 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∃ j : G1 F n →* G1 E n, Topology.IsClosedEmbedding j ∧
        (∀ t : G1 F n, ((j t : G1 E n) : AdelicGLn.AdelicGL E n) = mapGL n (adeleMap F E) (t : AdelicGLn.AdelicGL F n)) ∧
        ∀ t : AdelicGLn.AdelicGL F n, mapGL n (adeleMap F E) t ∈ normOneGL (K := E) (n := n) → t ∈ normOneGL (K := F) (n := n) := by
  intro h5 F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hemb, hdet, -⟩ := h5 F E σ hσ n hn
  have hpos : Module.finrank F E ≠ 0 := by
    haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
    exact Module.finrank_pos.ne'
  have key : ∀ t : AdelicGLn.AdelicGL F n,
      mapGL n (adeleMap F E) t ∈ normOneGL (K := E) (n := n) ↔ t ∈ normOneGL (K := F) (n := n) := by
    intro t
    rw [mem_normOneGL_iff_detModule, mem_normOneGL_iff_detModule, Subtype.ext_iff, Subtype.ext_iff]
    rw [hdet t]
    exact pow_eq_one_iff_of_nonneg (detModule F n t).2.le hpos
  let j : normOneGL (K := F) (n := n) →* normOneGL (K := E) (n := n) :=
    MonoidHom.codRestrict ((mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n →* AdelicGLn.AdelicGL E n).comp
      (normOneGL (K := F) (n := n)).subtype) (normOneGL (K := E) (n := n)) (fun t => (key t.1).2 t.2)
  refine ⟨j, ?_, fun t => rfl, fun t ht => (key t).1 ht⟩
  have hF : Topology.IsClosedEmbedding (Subtype.val : normOneGL (K := F) (n := n) → AdelicGLn.AdelicGL F n) :=
    (isClosed_normOneGL (K := F) (n := n)).isClosedEmbedding_subtypeVal
  have hE : Topology.IsEmbedding (Subtype.val : normOneGL (K := E) (n := n) → AdelicGLn.AdelicGL E n) :=
    Topology.IsEmbedding.subtypeVal
  have hc : Topology.IsClosedEmbedding ((Subtype.val : normOneGL (K := E) (n := n) → AdelicGLn.AdelicGL E n) ∘ j) :=
    hemb.comp hF
  exact Topology.IsClosedEmbedding.of_comp hE hc
end

section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.quotientIntegral_lt_top_of_invariant_closedEmbedding :
    Q1 → Q2 → ∀ (G T : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (H : Subgroup G) [LocallyCompactSpace H], IsClosed (H : Set G) →
        ∀ (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] [ν.IsMulRightInvariant]
          (i : T →* H), Topology.IsClosedEmbedding i → ∀ Φ : H → ℂ, Continuous Φ → (∀ t x, Φ (i t * x) = Φ x) →
          (∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤) →
          quotInt μ (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν Φ = quotInt μ id i ν Φ := by
  intro q1 q2 G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ hH μ _ ν _ _ _ i hi Φ hΦ hinv hfin
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨ρ, hρc, hρ, -⟩ := q2 H T ν i hi
  have hemb : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hH.measurableSet
  have hex : ∃ ρ', IsNormAlong (fun x : H => (x : G)) (fun t => ((i t : H) : G)) ν ρ' := by
    refine ⟨Function.extend (Subtype.val : H → G) (fun x => (ρ x : ℝ≥0∞)) 0,
      hemb.measurable_extend hρ.1 measurable_zero, fun x => ?_⟩
    rw [← hρ.2 x]
    refine lintegral_congr fun t => ?_
    exact Subtype.val_injective.extend_apply (fun x => (ρ x : ℝ≥0∞)) 0 (i t * x)
  have hn : IsNormAlong id i ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => hex.choose_spec.2 x⟩
  have h1 := q1 H H T μ ν (MonoidHom.id H) i measurable_id hi.continuous Φ
    (fun x : H => hex.choose (x : G)) hΦ.measurable hinv hn (hfin _ hn)
  refine Eq.trans ?_ h1.symm
  unfold quotInt
  rw [dite_eq_left hex]
  rfl
end
