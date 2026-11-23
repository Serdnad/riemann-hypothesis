module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory NumberField IsDedekindDomain Topology Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.orbitalSideBaseField_of_absoluteConvergence :
    SideAbs → RPF → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → InfF → SideF := by
  intro hS hRP hRC hUL hUO hTC hSep hCL hInf F _ _ n hn _ _ _ _ μ μi m hμ hμi hm γ hγ ν νi nv hν hνi hnv S a b ha hb hT hE
    fi f hfi hfc hf hloc
  have hcA : IsClosed ((TA γ : Subgroup (GA F n)) : Set (GA F n)) := Set.isClosed_centralizer _
  have hcI : IsClosed ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F))) :=
    Set.isClosed_centralizer _
  have hcF : ∀ v : Pl F, IsClosed ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) :
      Set (GL (Fin n) (v.adicCompletion F))) := fun v => Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (TA γ) := hcA.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := hcI.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) := fun v => (hcF v).locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology
    ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology
    ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))
  have hR := hRP F n
  have hRT := hRC _ _ _ _ (pI F n) (pF F n) (KF F n) hR (AdelicGLn.diagonal F n γ)
  obtain ⟨hc1, hc2, hc3, -⟩ := hTC F n γ hγ
  obtain ⟨hUi, hUv⟩ := hUL (Pl F) (GA F n) _ _ (pI F n) (pF F n) (KF F n) hR μ μi m hμ hμi hm
  have hP : Pair μ (TA γ).subtype ν := ⟨hμ, hcA.isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 hc1⟩
  have hPi : Pair μi (TI γ).subtype νi := ⟨hUi, hcI.isClosedEmbedding_subtypeVal, (hUO _ νi hνi).2 hc2⟩
  have hPv : ∀ v : Pl F, Pair (m v) (TF γ v).subtype (nv v) := fun v =>
    ⟨hUv v, (hcF v).isClosedEmbedding_subtypeVal, (hUO _ (nv v) (hnv v)).2 (hc3 v)⟩
  have hz : Continuous (zA F n) :=
    (continuous_centralSection (K := F) (n := n)).comp
      (Continuous.subtype_mk Real.continuous_exp fun s => Real.exp_pos s)
  have hzv : ∀ (v : Pl F) (s : ℝ), pF F n v (zA F n s) = 1 := fun v s => (hCL F n _).2.2.1 v
  have hfix : ∀ t : TA γ, ((TA γ).subtype t)⁻¹ * AdelicGLn.diagonal F n γ * (MonoidHom.id (GA F n)) ((TA γ).subtype t) =
      AdelicGLn.diagonal F n γ := by
    intro t
    have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
    simp only [Subgroup.subtype_apply, MonoidHom.id_apply]
    first
      | rw [mul_assoc, ← h, inv_mul_cancel_left]
      | rw [mul_assoc, h, inv_mul_cancel_left]
  have hcpt : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ C : Set (GL (Fin n) (InfiniteAdeleRing F)),
      IsCompact C ∧ ∀ x, x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ D →
        ∃ t : TI γ, ∃ y ∈ C, x = (TI γ).subtype t * y := by
    intro D hD
    obtain ⟨C, hC, h⟩ := (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).2 (hSep F n γ hγ).1 D hD
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := h x hx
    exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
  have hbd : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ B : Set ℝ, IsCompact B ∧
      ∀ s x, pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x) ∈ D → s ∈ B :=
    (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).1
  have hl : ∀ v ∉ S, f v = (KF F n v : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 ∧
      ∀ x, x⁻¹ * pF F n v (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ KF F n v ↔
        ∃ t : TF γ v, ∃ y ∈ KF F n v, x = (TF γ v).subtype t * y := by
    intro v hv
    refine ⟨(hloc v hv).1, fun x => ?_⟩
    refine ((hloc v hv).2 x).trans ⟨?_, ?_⟩
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
    · rintro ⟨t, y, hy, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
      exact ⟨t, by first | exact h | exact h.symm, y, hy, rfl⟩
  obtain ⟨hm1, hm2⟩ := hS (Pl F) (GA F n) (GL (Fin n) (InfiniteAdeleRing F)) (fun v => GL (Fin n) (v.adicCompletion F))
    (pI F n) (pF F n) (KF F n) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hR hRT (TA γ).subtype (TI γ).subtype (fun v => (TF γ v).subtype)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) μ μi m ν νi nv hP hPi hPv S a b ha hb hE hT
    (MonoidHom.id _) (MonoidHom.id _) (fun _ => MonoidHom.id _) (fun _ => rfl) (fun _ _ => rfl)
    continuous_id (fun _ => continuous_id) (AdelicGLn.diagonal F n γ) (zA F n) hz hzv hfix hcpt hbd fi f hfi hfc hf hl
  refine ⟨hm1, ?_⟩
  refine Eq.trans hm2 ?_
  congr 3
  funext s
  congr 1
  funext x
  have hc := (hCL F n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  congr 1
  change pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * x) =
    x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x
  rw [mul_assoc, mul_assoc, ← mul_assoc (pI F n (zA F n s)), hc x⁻¹, mul_assoc, mul_assoc]
end

section

open NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open scoped NumberField.AdeleRing RestrictedProduct

namespace UpperTheory.OpenSubgroupProjection

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

private abbrev RF : Type :=
  Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]

private theorem fst_eq (g : GA K n) : (AdelicGLn.prodEquiv K n g).1 = pI K n g := by
  apply Units.ext; ext a b; rfl

private theorem opn (v : Pl K) : IsOpen (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isOpen_integralGL _ n

private theorem cpt (v : Pl K) : IsCompact (KF K n v : Set (GL (Fin n) (v.adicCompletion K))) :=
  GLnLocal.isCompact_integralGL _ n

private noncomputable def phi : GA K n ≃ₜ GL (Fin n) (InfiniteAdeleRing K) × RF K n :=
  (AdelicGLn.prodEquiv K n).toHomeomorph.trans
    (Homeomorph.prodCongr (Homeomorph.refl _) (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph)

private theorem phi_fst (g : GA K n) : (phi K n g).1 = pI K n g := fst_eq K n g

private theorem phi_snd (g : GA K n) (v : Pl K) : (phi K n g).2 v = pF K n v g := rfl

private theorem compact_box (C : ∀ v : Pl K, Set (GL (Fin n) (v.adicCompletion K)))
    (hC : ∀ v, IsCompact (C v))
    (hK : ∀ᶠ v in cofinite, C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))) :
    IsCompact {x : RF K n | ∀ v, x v ∈ C v} := by
  let A : Set (Pl K) := {v | C v ⊆ (KF K n v : Set (GL (Fin n) (v.adicCompletion K)))}
  have hle : (cofinite : Filter (Pl K)) ≤ 𝓟 A := le_principal_iff.2 hK
  have hemb : IsEmbedding (DFunLike.coe : (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := RestrictedProduct.isEmbedding_coe_of_principal
  have hT : IsCompact (Set.pi Set.univ C) := isCompact_univ_pi hC
  have hsub : Set.pi Set.univ C ⊆ Set.range (DFunLike.coe :
      (Πʳ v : Pl K, [GL (Fin n) (v.adicCompletion K), KF K n v]_[𝓟 A]) →
      ∀ v : Pl K, GL (Fin n) (v.adicCompletion K)) := fun x hx =>
    ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v trivial)⟩, rfl⟩
  have h1 := (hemb.isInducing.isCompact_preimage_iff hsub).2 hT
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hle)
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, eventually_principal.2 fun v hv => hv (hx v)⟩, fun v _ => hx v, rfl⟩
  · rintro ⟨y, hy, rfl⟩ v
    exact hy v trivial

private theorem opnU (S : Finset (Pl K)) :
    IsOpen (US (pF K n) (KF K n) S : Set (GA K n)) := by
  have h0 : IsOpen (US (pF K n) (KF K n) ∅ : Set (GA K n)) := by
    have : (US (pF K n) (KF K n) ∅ : Set (GA K n)) =
        (fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹'
          (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, AdelicGLn.mem_integralFiniteGL_iff_forall, mem_US]
      exact ⟨fun h v => h v (Finset.notMem_empty v), fun h v _ => h v⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).preimage
      (continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous)
  exact Subgroup.isOpen_mono (H₁ := US (pF K n) (KF K n) ∅) (H₂ := US (pF K n) (KF K n) S)
    (fun g hg v _ => hg v (Finset.notMem_empty v)) h0

end UpperTheory.OpenSubgroupProjection

open UpperTheory.OpenSubgroupProjection in
theorem UpperTheory.restrictedProduct_finite_adelicGL :
    RPF := by
  intro K _ _ n
  refine
    { cq := ?_
      cp := fun v => continuous_finAt v
      opn := opn K n
      cpt := cpt K n
      ae := fun g => AdelicGLn.eventually_mem_integralGL K n g
      opnU := opnU K n
      ext := ?_
      surj := ?_
      prop := ?_ }
  · have : (pI K n : GA K n → _) = fun g => (AdelicGLn.prodEquiv K n g).1 :=
      funext fun g => (fst_eq K n g).symm
    rw [this]
    exact continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous
  · intro g g' h1 h2
    apply (phi K n).injective
    refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
    · rw [phi_fst, phi_fst, h1]
    · exact h2 v
  · intro gi gv h
    refine ⟨(phi K n).symm (gi, ⟨gv, h⟩), ?_, fun v => ?_⟩
    · rw [← phi_fst, Homeomorph.apply_symm_apply]
    · rw [← phi_snd, Homeomorph.apply_symm_apply]
      rfl
  · intro Ci C hCi hC hK
    have h := (hCi.prod (compact_box K n C hC hK))
    have h2 := (phi K n).isCompact_preimage.2 h
    convert h2 using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, phi_fst, phi_snd]
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Topology Filter

private theorem ce_of_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) (h : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hf (Function.Injective.of_comp h.injective)
    (isProperMap_of_comp_of_t2 hf hg h.isProperMap).isClosedMap

private theorem ce_reindex {V : Type*} {A : V → Type*} [∀ v, TopologicalSpace (A v)] (φ : V → V) (h : ∀ v, φ v = v) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => x (φ v)) := by
  obtain rfl : φ = id := funext h
  exact (Homeomorph.refl _).isClosedEmbedding

private theorem ce_piMap {V : Type*} {A B : V → Type*} [∀ v, TopologicalSpace (A v)] [∀ v, TopologicalSpace (B v)]
    (ι : ∀ v, A v → B v) (h : ∀ v, IsClosedEmbedding (ι v)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => ι v (x v)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_pi fun v => (h v).continuous.comp (continuous_apply v))
    (fun _ _ e => funext fun v => (h v).injective (congrFun e v))
    (IsProperMap.pi_map fun v => (h v).isProperMap).isClosedMap

private theorem ce_pi {V W : Type*} (c : W → V) (hc : Function.Surjective c) {A : V → Type*} {B : W → Type*}
    [∀ v, TopologicalSpace (A v)] [∀ w, TopologicalSpace (B w)] [∀ w, T2Space (B w)]
    (ι : ∀ w, A (c w) → B w) (h : ∀ w, IsClosedEmbedding (ι w)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (w : W) => ι w (x (c w))) := by
  choose s hs using hc
  refine ce_of_comp (g := fun (y : ∀ w, B w) (v : V) => y (s v))
    (continuous_pi fun w => (h w).continuous.comp (continuous_apply _))
    (continuous_pi fun v => continuous_apply _) ?_
  exact (ce_piMap (fun v => ι (s v)) fun v => h (s v)).comp (ce_reindex (A := A) (fun v => c (s v)) hs)

private theorem ce_gl {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [T2Space R] [T2Space S] (n : ℕ) (f : R →+* S) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mapGL n f) := by
  have h1 : IsClosedEmbedding (fun (x : Fin n → R) (j : Fin n) => f (x j)) := ce_piMap (fun _ => f) fun _ => hf
  have hM : IsClosedEmbedding (f.mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) S) :=
    ce_piMap (fun _ => fun (x : Fin n → R) (j : Fin n) => f (x j)) fun _ => h1
  exact @IsClosedEmbedding.units_map (Matrix (Fin n) (Fin n) R) (Matrix (Fin n) (Fin n) S)
    _ _ _ _ _ _ f.mapMatrix.toMonoidHom hM

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_small (v : HeightOneSpectrum (𝓞 F)) (g : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ a : v.adicCompletion F, a ≠ 0 ∧ Valued.v a < (g : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hπ
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) π) < 1 := by
    rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h2 g
  refine ⟨algebraMap F (v.adicCompletion F) π ^ k, pow_ne_zero _ ?_, by rwa [map_pow]⟩
  intro h0
  rw [h0, map_zero] at h1
  exact (WithZero.exp_ne_zero) h1.symm

private theorem ce_compl (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    IsClosedEmbedding (completionMap v w) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  have hind : IsInducing (completionMap v w) := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    · have := (continuous_completionMap v w).tendsto 0
      rw [map_zero] at this
      exact this.le_comap
    · intro s hs
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
      let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
      let emb : ν.ValueGroup₀ →*₀ WithZero (Multiplicative ℤ) :=
        MonoidWithZeroHom.ValueGroup₀.embedding (f := ν.toMonoidWithZeroHom)
      obtain ⟨a, ha0, ha⟩ := exists_small v (Units.map emb.toMonoidHom γ)
      have hfa : completionMap v w a ≠ 0 := (map_ne_zero_iff _ (completionMap v w).injective).2 ha0
      have hopen := Valued.isOpen_ball (w.adicCompletion E) ((Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a))
      have hmem : (0 : w.adicCompletion E) ∈ {x | (Valued.v : Valuation (w.adicCompletion E) _).restrict x < (Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a)} := by
        simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_zero]
        exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hfa)
      refine Filter.mem_comap.2 ⟨_, hopen.mem_nhds hmem, fun x hx => hγ ?_⟩
      have h1 : Valued.v (completionMap v w x) < Valued.v (completionMap v w a) := by
        simpa [Valuation.restrict_lt_iff] using hx
      rw [valued_completionMap, valued_completionMap] at h1
      have h2 := lt_of_pow_lt_pow_left₀ _ zero_le h1
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      exact h2.trans ha
  have hu : IsUniformInducing (completionMap v w) := AddMonoidHom.isUniformInducing_of_isInducing hind
  exact (IsUniformEmbedding.mk hu (completionMap v w).injective).isClosedEmbedding

omit [NumberField F] [NumberField E] in
private theorem ce_infComp (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] :
    IsClosedEmbedding (AbsoluteValue.Completion.map v.1 w.1) :=
  (AbsoluteValue.Completion.isometry_map v.1 w.1).isClosedEmbedding

private theorem ce_incFin (v : HeightOneSpectrum (𝓞 F)) : IsClosedEmbedding (incFin E v) := by
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  let w : PlacesOver E v := (placesOverEquiv E v).symm P
  exact ce_of_comp (g := fun y : CompletionsOver E v => y w)
    (continuous_pi fun u => continuous_completionMap v u.1) (continuous_apply w) (ce_compl v w.1)

open scoped NumberField.LiesOver in
private theorem ce_infMap : IsClosedEmbedding (infMap F E) := by
  have hs : Function.Surjective (fun w : InfinitePlace E => w.comap (algebraMap F E)) := InfinitePlace.comap_surjective
  have hmap : (infMap F E : InfiniteAdeleRing F → InfiniteAdeleRing E) =
      fun (x : InfiniteAdeleRing F) (w : InfinitePlace E) =>
        AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (x (w.comap (algebraMap F E))) := by
    funext x w
    exact (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w).trans
      (AbsoluteValue.Completion.algebraMap_apply_of_liesOver (w.comap (algebraMap F E)).1 w.1 _)
  rw [hmap]
  exact ce_pi (A := fun v : InfinitePlace F => v.Completion) (B := fun w : InfinitePlace E => w.Completion)
    (fun w : InfinitePlace E => w.comap (algebraMap F E)) hs
    (fun w => AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1) fun w => ce_infComp _ w
end

theorem UpperTheory.adele_baseChange_local_isClosedEmbedding :
    LocEmb := by
  intro F E _ _ _ _ _ n
  exact ⟨ce_gl n _ ce_infMap, fun v => ce_gl n _ (ce_incFin v)⟩
end

section

open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem pow_fix {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z) (m : ℕ) :
    (θ ^ m) z = z := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply, hz, ih]

private theorem twNorm_central {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z)
    (hc : ∀ g, z * g = g * z) (m : ℕ) (δ : G) :
    twNorm θ m (z * δ) = z ^ m * twNorm θ m δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, ih, map_mul, pow_fix θ z hz m, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (twNorm θ m δ) z, ← hc (twNorm θ m δ), mul_assoc]

theorem UpperTheory.twistedNorm_central_of_baseChange_compat :
    Compat → CentLoc → CentBC → ZNorm := by
  intro hC hL hB F E _ _ _ _ _ _ σ _ n _ s δ
  have hl : (Module.finrank F E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank F E := Module.finrank_pos
    exact_mod_cast this.ne'
  have c3 := (hC F E σ n).2.2.1
  have c6 := (hC F E σ n).2.2.2.2.2.1

  have e1 : (⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) ^ Module.finrank F E
      = ⟨Real.exp s, Real.exp_pos s⟩ := by
    apply Subtype.ext
    have : ((⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) = Real.exp (s / Module.finrank F E) ^ Module.finrank F E := rfl
    rw [this, ← Real.exp_nat_mul, mul_div_cancel₀ _ hl]
  have hz : pI E n (zA E n s) =
      mapGL n (infMap F E) (pI F n (zA F n (s / Module.finrank F E))) := by
    rw [← c3, hB F E n, e1]
  have hfix : mapGL n (galInf σ) (pI E n (zA E n s)) = pI E n (zA E n s) := by
    rw [hz]; exact c6 _
  have hcen := (hL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  have hpow : pI E n (zA E n s) ^ Module.finrank F E =
      mapGL n (infMap F E) (pI F n (zA F n s)) := by
    rw [← c3, hB F E n, ← map_pow, ← map_pow]
  exact (twNorm_central (mapGL n (galInf σ)) _ hfix hcen _ δ).trans (by rw [hpow])
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct

private theorem galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B) :
    galOf e (1 : E ≃ₐ[F] E) = RingHom.id _ := by
  ext x
  have h : Algebra.TensorProduct.map (((1 : E ≃ₐ[F] E) : E →ₐ[F] E)) (AlgHom.id F A) = AlgHom.id F _ := by
    ext <;> simp
  simp only [galOf, RingHom.comp_apply, h]
  simp

private theorem infMap_self (F : Type) [Field F] [NumberField F] : infMap F F = RingHom.id _ := by
  have hd := InfiniteAdeleRing.denseRange_algebraMap F
  have h1 : Continuous (infMap F F) := InfinitePlace.continuous_infiniteAdeleRingMap
  have := hd.equalizer h1 continuous_id (funext fun k => by
    simpa using InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := F) k)
  exact RingHom.ext fun x => congrFun this x

private theorem incFin_bij (F : Type) [Field F] [NumberField F] (v : Pl F) : Function.Bijective (incFin F v) := by
  have h : ∀ x, incFin F v x = tensorEquiv' F v ((1 : F) ⊗ₜ[F] x) := by
    intro x
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hb : Function.Bijective (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) :=
    (TensorProduct.lid F (v.adicCompletion F)).symm.bijective
  have : (incFin F v : _ → _) = tensorEquiv' F v ∘ (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) := funext h
  rw [this]
  exact (tensorEquiv' F v).bijective.comp hb

theorem UpperTheory.baseChange_trivial_extension :
    Triv := by
  intro F _ _
  refine ⟨galOf_one' _, infMap_self F, fun v => ⟨galOf_one' _, incFin_bij F v⟩⟩
end

section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal GroundTheory.Automorphic ValuativeRel

private theorem mem_integers_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem completionMap_mem_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (x : v.adicCompletion F) :
    completionMap v w.1 x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := by
  rw [mem_integers_iff, mem_integers_iff, valued_completionMap]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'

theorem UpperTheory.adicCompletion_integers_baseChange_iff :
    UnitIff := by
  intro F E _ _ _ _ _ n v t
  have key : ∀ w : PlacesOver E v,
      mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) t) ∈
        GLnLocal.integralGL (w.1.adicCompletion E) n ↔ t ∈ KF F n v := by
    intro w
    have hc : ∀ s : GL (Fin n) (v.adicCompletion F),
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) s) =
          mapGL n (completionMap v w.1) s := fun s => Units.ext (Matrix.ext fun i j => rfl)
    rw [hc, GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => completionMap_mem_iff v w _)
      (forall₂_congr fun i j => completionMap_mem_iff v w _)
  constructor
  · intro h
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    let w : PlacesOver E v := ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 h
end
