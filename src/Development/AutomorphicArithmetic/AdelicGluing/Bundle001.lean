module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_atFin {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

private theorem fin_above (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem eq_one_of_cmp {v : Pl F} (g : GL (Fin n) (CompletionsOver E v))
    (h : ∀ w : PlacesOver E v, cmp w g = 1) : g = 1 := by
  apply Units.ext
  ext i j w
  have h1 : (g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i j w =
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j :=
    congrArg (fun x : GL (Fin n) (w.1.adicCompletion E) => (x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) (h w)
  rw [h1]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem cont_fin (w : Pl E) : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
    (finAt w (finEmb E n h) : GL (Fin n) (w.adicCompletion E)) :=
  (_root_.RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous

private theorem cont_above (v : Pl F) : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
    mapGL n (atFin (E := E) v) (finEmb E n h) := by
  have hval : Continuous fun h : AdelicGLn.FiniteAdelicGL E n =>
      Units.val (mapGL n (atFin (E := E) v) (finEmb E n h)) := by
    refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.comp (cont_fin w.1)).matrix_elem i j
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have h2 := hval.comp (continuous_inv (G := AdelicGLn.FiniteAdelicGL E n))
  refine h2.congr fun h => ?_
  simp only [Function.comp, map_inv]

private theorem comp_mem (P : ∀ w : Pl E, Subgroup (GL (Fin n) (w.adicCompletion E))) (w : Pl E)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ P w) (w' : Pl E) :
    finAt w' (finEmb E n (AdelicGLn.localEmbedding w g)) ∈ P w' := by
  obtain ⟨-, h1, h2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  by_cases hw : w' = w
  · subst hw
    rw [h1]
    exact hg
  · rw [h2 w' hw]
    exact one_mem _

private theorem above_one (w : Pl E) (g : GL (Fin n) (w.adicCompletion E)) (v : Pl F)
    (hne : w.under (𝓞 F) ≠ v) :
    mapGL n (atFin (E := E) v) (finEmb E n (AdelicGLn.localEmbedding w g)) = 1 := by
  obtain ⟨-, -, h2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w
  refine eq_one_of_cmp _ fun w' => ?_
  rw [cmp_atFin]
  exact h2 w'.1 (fun h => hne (by rw [← h]; exact under_over w')) g

end SlopeTestRemainingChoices

theorem UpperTheory.baseChangeLevel_isOpen_isCompact_contains_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (q : Pl F) (w₀ : PlacesOver E q) (L : Loc σ n q w₀),
          {w : Pl E | w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q}.Finite ∧
          IsOpen (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) ∧ IsCompact (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) ∧
          levE L.UE ≤ AdelicGLn.integralFiniteGL E n ∧
          (∀ w : Pl E, ¬ (w.under (𝓞 F) ∈ L.S ∨ w.under (𝓞 F) = q) → (GLnLocal.integralGL (w.adicCompletion E) n).map (AdelicGLn.localEmbedding w) ≤ levE L.UE) ∧
          ∀ w : PlacesOver E q, (GLnLocal.iwahori (w.1.adicCompletion E) n).map (AdelicGLn.localEmbedding w.1) ≤ levE L.UE ∧
            ∀ u ∈ levE L.UE, finAt w.1 (finEmb E n u) ∈ GLnLocal.iwahori (w.1.adicCompletion E) n := by
  classical
  intro F E _ _ _ _ _ _ σ n hn q w₀ L
  have hmem : ∀ u : AdelicGLn.FiniteAdelicGL E n,
      u ∈ levE L.UE ↔ ∀ v, mapGL n (atFin (E := E) v) (finEmb E n u) ∈ L.UE v := by
    intro u
    simp only [levE, Subgroup.mem_iInf, Subgroup.mem_comap]
    rfl
  have hiq : ∀ g, g ∈ L.UE q ↔ ∀ w, cmp w g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n := L.at_q.2.2.1
  have hU : ∀ v, ∀ g ∈ L.UE v, g ∈ unitSet E n v := by
    intro v g hg
    by_cases hv : v ∈ L.S
    · exact (L.lev v hv).2.1 hg
    by_cases hvq : v = q
    · subst hvq
      intro w
      exact GLnLocal.iwahori_le_integralGL _ _ ((hiq g).1 hg w)
    · have h3 : g ∈ (L.UE v : Set _) := hg
      rwa [(L.off v hv hvq).2.2.1] at h3
  have hint : levE L.UE ≤ AdelicGLn.integralFiniteGL E n := by
    intro u hu
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro w
    have h2 : cmp (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F)))
        (mapGL n (atFin (E := E) (w.under (𝓞 F))) (finEmb E n u)) ∈ GLnLocal.integralGL (w.adicCompletion E) n :=
      hU _ _ ((hmem u).1 hu (w.under (𝓞 F))) ⟨w, ⟨rfl⟩⟩
    rw [cmp_atFin] at h2
    exact h2
  have hVo : IsOpen (((AdelicGLn.integralFiniteGL E n : Set (AdelicGLn.FiniteAdelicGL E n)) ∩
      ⋂ v ∈ L.S, (fun h : AdelicGLn.FiniteAdelicGL E n => mapGL n (atFin (E := E) v) (finEmb E n h)) ⁻¹'
        (L.UE v : Set (GL (Fin n) (CompletionsOver E v)))) ∩
      ⋂ w : PlacesOver E q, (fun h : AdelicGLn.FiniteAdelicGL E n =>
        (finAt w.1 (finEmb E n h) : GL (Fin n) (w.1.adicCompletion E))) ⁻¹'
          (GLnLocal.iwahori (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E)))) :=
    ((AdelicGLn.isOpen_integralFiniteGL E n).inter
      (isOpen_biInter_finset fun v hv => (L.lev v hv).1.preimage (cont_above v))).inter
      (isOpen_iInter_of_finite fun w => (GLnLocal.isOpen_iwahori _ n).preimage (cont_fin w.1))
  have hopen : IsOpen (levE L.UE : Set (AdelicGLn.FiniteAdelicGL E n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levE L.UE) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨⟨one_mem _, ?_⟩, ?_⟩
      · simp only [Set.mem_iInter]
        intro v _
        exact (hmem 1).1 (one_mem _) v
      · simp only [Set.mem_iInter]
        intro w
        have h1 : finAt w.1 (finEmb E n (1 : AdelicGLn.FiniteAdelicGL E n)) = 1 := by
          rw [map_one, finAt_one]
        simp only [Set.mem_preimage, h1]
        exact one_mem _
    · rintro h ⟨⟨h1, h2⟩, h3⟩
      simp only [Set.mem_iInter] at h2 h3
      refine (hmem h).2 fun v => ?_
      by_cases hv : v ∈ L.S
      · exact h2 v hv
      by_cases hvq : v = q
      · subst hvq
        refine (hiq _).2 fun w => ?_
        rw [cmp_atFin]
        exact h3 w
      · have h4 : mapGL n (atFin (E := E) v) (finEmb E n h) ∈ (L.UE v : Set _) := by
          rw [(L.off v hv hvq).2.2.1]
          intro w
          change cmp w _ ∈ _
          rw [cmp_atFin]
          exact (AdelicGLn.mem_integralFiniteGL_iff_forall E n).1 h1 w.1
        exact h4
  refine ⟨?_, hopen, ?_, hint, ?_, ?_⟩
  · refine (Set.Finite.biUnion (insert q L.S).finite_toSet
      (fun v _ => fin_above (E := E) v)).subset fun w hw => ?_
    simp only [Set.mem_iUnion]
    refine ⟨w.under (𝓞 F), ?_, rfl⟩
    rcases hw with h | h
    · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem h)
    · exact Finset.mem_coe.2 (Finset.mem_insert.2 (Or.inl h))
  · exact (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w hw _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe] at hg; rw [hmem]
    intro v
    by_cases hv : w.under (𝓞 F) = v
    · subst hv
      rw [not_or] at hw
      have h4 : mapGL n (atFin (E := E) (w.under (𝓞 F))) (finEmb E n (AdelicGLn.localEmbedding w g)) ∈
          (L.UE (w.under (𝓞 F)) : Set _) := by
        rw [(L.off _ hw.1 hw.2).2.2.1]
        intro w'
        change cmp w' _ ∈ _
        rw [cmp_atFin]
        exact comp_mem (fun w => GLnLocal.integralGL (w.adicCompletion E) n) w hg w'.1
      exact h4
    · rw [above_one w g v hv]
      exact one_mem _
  · intro w
    refine ⟨?_, fun u hu => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe] at hg; rw [hmem]
      intro v
      by_cases hv : v = q
      · subst hv
        refine (hiq _).2 fun w' => ?_
        rw [cmp_atFin]
        exact comp_mem (fun w => GLnLocal.iwahori (w.adicCompletion E) n) w.1 hg w'.1
      · rw [above_one w.1 g v (by rw [under_over]; exact Ne.symm hv)]
        exact one_mem _
    · have h5 := (hiq _).1 ((hmem u).1 hu q) w
      rwa [cmp_atFin] at h5
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

theorem UpperTheory.levF_isOpen_isCompact_le_integral :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (lev : ∀ v : Pl K, Subgroup (GL (Fin n) (v.adicCompletion K))) (S : Finset (Pl K)),
      (∀ v ∈ S, IsOpen (lev v : Set (GL (Fin n) (v.adicCompletion K))) ∧ lev v ≤ GLnLocal.integralGL (v.adicCompletion K) n) →
      (∀ v, v ∉ S → lev v = GLnLocal.integralGL (v.adicCompletion K) n) →
      IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
        levF lev ≤ AdelicGLn.integralFiniteGL K n ∧
        ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), J ≤ lev w → J.map (AdelicGLn.localEmbedding w) ≤ levF lev := by
  classical
  intro K _ _ n lev S hS hS'
  have hmem : ∀ h : AdelicGLn.FiniteAdelicGL K n,
      h ∈ levF lev ↔ ∀ v, AdelicGLn.finiteRestrictedEquiv K n h v ∈ lev v := fun h => Iff.rfl
  have hint : levF lev ≤ AdelicGLn.integralFiniteGL K n := by
    intro h hh
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro v
    have hv := (hmem h).1 hh v
    by_cases hvS : v ∈ S
    · exact (hS v hvS).2 hv
    · rwa [hS' v hvS] at hv
  have hev : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n =>
      (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K)) := fun v =>
    (_root_.RestrictedProduct.continuous_eval v).comp (AdelicGLn.finiteRestrictedEquiv K n).continuous
  have hVo : IsOpen ((AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
      ⋂ v ∈ S, (fun h : AdelicGLn.FiniteAdelicGL K n =>
        (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K))) ⁻¹'
          (lev v : Set (GL (Fin n) (v.adicCompletion K)))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (isOpen_biInter_finset fun v hv => (hS v hv).1.preimage (hev v))
  have hopen : IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levF lev) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨one_mem _, ?_⟩
      simp only [Set.mem_iInter]
      intro v _
      exact (levF lev).one_mem v
    · rintro h ⟨h1, h2⟩
      simp only [Set.mem_iInter] at h2
      refine (hmem h).2 fun v => ?_
      by_cases hvS : v ∈ S
      · exact h2 v hvS
      · rw [hS' v hvS]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1 v
  refine ⟨hopen, ?_, hint, ?_⟩
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w J hJ _ ⟨x, hx, rfl⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1
    have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hJ hx
    · rw [h2 v hv]
      exact one_mem _
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

section SlopeTestRemainingChoices

open GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct ValuativeRel

private theorem galAd_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : galAd σ a = σ • a := by
  have h1 : (MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ) = Formalism.L2.Host.CT.adMap σ.toRingEquiv :=
    UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv _ (continuous_const_smul σ) fun x => GroundTheory.Global.AdeleBaseChange.smul_algebraMap σ x
  rw [UpperTheory.ConvolutionTheory.K.galAdEq, ← h1]
  rfl

variable {E : Type} [Field E] [NumberField E]

private theorem v_lt (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem v_le (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem v_eq (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, v_le, ← not_lt (b := 1) (a := ‖y‖), ← v_lt, not_lt]

private theorem unif_lt (w : HeightOneSpectrum (𝓞 E)) : ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ < 1 := by
  rw [← v_lt]
  have h := GLnLocal.irreducible_uniformizer (w.adicCompletion E)
  refine lt_of_le_of_ne (GLnLocal.uniformizer (w.adicCompletion E)).2 fun e => h.not_isUnit ?_
  exact (Valuation.integer.integers (ValuativeRel.valuation (w.adicCompletion E))).isUnit_of_one' e

private theorem unif_max (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) (hy : ‖y‖ < 1) :
    ‖y‖ ≤ ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ := by
  have h := GLnLocal.irreducible_uniformizer (w.adicCompletion E)
  let z : 𝒪[w.adicCompletion E] := ⟨y, ((v_lt w y).2 hy).le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := fun hu =>
    ((v_lt w y).2 hy).ne ((Valuation.integer.integers (ValuativeRel.valuation (w.adicCompletion E))).one_of_isUnit hu)
  rw [h.maximalIdeal_eq, Ideal.mem_span_singleton'] at hz
  obtain ⟨a, ha⟩ := hz
  have e : y = a.1 * (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) := (congrArg Subtype.val ha).symm
  rw [e, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((v_le w _).1 a.2)

end SlopeTestRemainingChoices

theorem UpperTheory.exists_galois_transport_localGL_preserving_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ w : Pl E,
          ∃ s : GL (Fin n) (w.adicCompletion E) ≃* GL (Fin n) ((σ • w).adicCompletion E),
            (∀ g, (mapGL n (galAd σ) (finEmb E n (AdelicGLn.localEmbedding w g)) : AdelicGLn.AdelicGL E n) = finEmb E n (AdelicGLn.localEmbedding (σ • w) (s g))) ∧
            (∀ g, g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔ s g ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n) ∧
            ∀ ν : Fin n → ℤ, s (Cartan.diagPow (w.adicCompletion E) n ν) ∈ iwCoset (σ • w) ν := by
  intro F E _ _ _ _ _ _ σ n _ w
  have h' : w = σ⁻¹ • (σ • w) := (inv_smul_smul σ w).symm
  let t : w.adicCompletion E ≃+* (σ • w).adicCompletion E :=
    RingEquiv.ofRingHom (galHom σ w (σ • w) rfl) (galHom σ⁻¹ (σ • w) w h')
      (galHom_comp_galHom σ⁻¹ σ (mul_inv_cancel σ) _ _ h' rfl) (galHom_comp_galHom σ σ⁻¹ (inv_mul_cancel σ) _ _ rfl h')
  have hc : ∀ a (u : Pl E), (galAd σ a).2 (σ • u) = galHom σ u (σ • u) rfl (a.2 u) := fun a u => by
    rw [galAd_smul]; exact AdeleBaseChange.smul_snd_eq_galHom σ a u _ rfl
  have hn : ∀ y, ‖t y‖ = ‖y‖ := fun y => by
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun y => ‖t y‖ = ‖y‖) y
      (isClosed_eq (continuous_norm.comp (continuous_galHom σ w _ rfl)) continuous_norm) fun l => ?_
    have h1 := (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (algebraMap E _ l)).1 w
    rw [hc] at h1
    exact h1
  let s : GL (Fin n) (w.adicCompletion E) ≃* GL (Fin n) ((σ • w).adicCompletion E) :=
    Units.mapEquiv t.mapMatrix.toMulEquiv
  have hs : ∀ g i j, s g i j = t (g i j) := fun _ _ _ => rfl
  refine ⟨s, fun g => ?_, fun g => ?_, fun ν => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
    · have e1 : ∀ (y : AdelicGLn.FiniteAdelicGL E n), (finEmb E n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j :=
        fun y => congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
      refine Eq.trans ?_ (e1 _).symm
      funext v
      change (galAd σ (finEmb E n (AdelicGLn.localEmbedding w g) i j)).1 v = _
      rw [galAd_smul, AdeleBaseChange.smul_fst, e1]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq]
        exact map_one _
      · simp only [Matrix.one_apply_ne hij]
        exact map_zero _
    · refine FiniteAdeleRing.ext _ fun v => ?_
      obtain ⟨u, rfl⟩ : ∃ u, v = σ • u := ⟨σ⁻¹ • v, (smul_inv_smul σ v).symm⟩
      refine (hc (finEmb E n (AdelicGLn.localEmbedding w g) i j) u).trans ?_
      change galHom σ u (σ • u) rfl (finAt u (finEmb E n (AdelicGLn.localEmbedding w g)) i j) =
        finAt (σ • u) (finEmb E n (AdelicGLn.localEmbedding (σ • w) (s g))) i j
      by_cases hu : u = w
      · subst hu
        rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n u).2.1, (UpperTheory.ConvolutionTheory.Tf.locEmb E n (σ • u)).2.1]
        rfl
      · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.2.1 u hu, (UpperTheory.ConvolutionTheory.Tf.locEmb E n (σ • w)).2.2.1 _ fun e => hu (MulAction.injective σ e)]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
  · simp only [GLnLocal.mem_iwahori_iff, v_lt, v_eq, hs, hn]
    refine and_congr (forall₂_congr fun i j => ?_) Iff.rfl
    exact ((v_le w _).trans (by rw [hn])).trans (v_le (σ • w) (t (g i j))).symm
  · set p := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hp
    set p' := (GLnLocal.uniformizer ((σ • w).adicCompletion E) : (σ • w).adicCompletion E) with hp'
    have h0 : p' ≠ 0 := Cartan.uniformizer_ne_zero _
    have h1 : ‖t p‖ = ‖p'‖ := le_antisymm (unif_max _ _ (by rw [hn]; exact unif_lt w)) (by
      rw [hn, ← t.apply_symm_apply p', hn]
      exact unif_max _ _ (by rw [← hn, t.apply_symm_apply]; exact unif_lt _))
    refine ⟨s (Cartan.diagPow _ n ν) * (Cartan.diagPow _ n ν)⁻¹, ?_, 1, one_mem _, by simp⟩
    have e : ((s (Cartan.diagPow _ n ν) * (Cartan.diagPow _ n ν)⁻¹ : GL (Fin n) ((σ • w).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((σ • w).adicCompletion E)) = Matrix.diagonal fun i => t p ^ ν i * p' ^ (-ν i) := by
      rw [← Matrix.diagonal_mul_diagonal, Units.val_mul]
      congr 1
      ext i j
      rw [hs, Cartan.coe_diagPow]
      by_cases hij : i = j
      · subst hij
        simp [hp]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h2 : ∀ i, ‖t p ^ ν i * p' ^ (-ν i)‖ = 1 := fun i => by
      rw [norm_mul, norm_zpow, norm_zpow, h1, ← zpow_add₀ (norm_ne_zero_iff.2 h0), add_neg_cancel, zpow_zero]
    refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
    · refine (v_le _ _).2 ?_
      rw [e]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, h2]
      · simp [Matrix.diagonal_apply_ne _ hij]
    · rw [v_lt, e, Matrix.diagonal_apply_ne _ (by rintro rfl; exact lt_irrefl _ hij)]
      simp
    · rw [v_eq, e, Matrix.diagonal_apply_eq, h2]
end
