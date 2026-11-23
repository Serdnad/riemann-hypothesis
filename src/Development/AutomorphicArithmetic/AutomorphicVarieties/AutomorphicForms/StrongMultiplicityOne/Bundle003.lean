module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (f : R →+* S) {k : GL (Fin n) R}
    (h : IsY m k.val) : IsY m (GeneralLinearGroup.map f k).val := by
  intro i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (k.val i i) = 1
    rw [(h i hi).1, map_one]
  · change f (k.val i j) = 0
    rw [(h i hi).2 j hj, map_zero]

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := by
  intro i _
  exact ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_of_cmp {E : Type} [Field E] [NumberField E] {n m : ℕ} {k : GL (Fin n) (Af E)}
    (h : ∀ w, IsY m (cmp w k).val) : IsY m k.val := by
  intro i hi
  refine ⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩
  · exact (h w i hi).1
  · exact (h w i hi).2 j hj

private theorem loc_comm {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {k : GL (Fin n) (Af E)} (hk : cmp w k = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    k * locGL E n w y = locGL E n w y * k := by
  refine cmp_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hk, one_mul, mul_one]
  · rw [show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]

private theorem supp_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {a b : GL (Fin n) (Af E)} (ha : SuppIn S a) (hb : SuppIn S b) : SuppIn S (a * b) := fun w hw => by
  rw [map_mul, ha w hw, hb w hw, mul_one]

private theorem supp_loc {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) (y : GL (Fin n) (w.adicCompletion E)) :
    SuppIn S (locGL E n w y) := fun v hv =>
  GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y

private theorem comb_mapDomain {G G' : Type} [Group G] [Group G'] (f : G →* G') (c : G →₀ ℂ) (W : G' → ℂ)
    (g : G') (p : G) : comb (c.mapDomain f) W (g * f p) = comb c (fun y => W (g * f y)) p := by
  unfold comb
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [map_mul, mul_assoc]

theorem UpperTheory.V.Af.StrongMultiplicityOne.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.FinKir := by
  classical
  intro hK hP hE E _ _ _ n hn S U
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact fun w _ => map_one _
    · obtain rfl : p = 1 := cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm
      unfold comb
      rw [Finsupp.sum_single_index (by simp), mul_one]
  | insert w S hw ih =>
    obtain ⟨c₁, H₁, h1, hs₁, hc₁⟩ := ih
    obtain ⟨hE1, -, -, hEc⟩ := hE E n 0
    obtain ⟨c₀, H₀, h0, hc₀⟩ := hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega)
      (U.comap (locGL E n w) (hEc w))
    obtain ⟨c, hs, hc⟩ := exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))
    have mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k :=
      fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)
    have hl : ∀ y, SuppIn (insert w S) (locGL E n w y) := supp_loc (Finset.mem_insert_self w S)
    refine ⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_,
      fun W hW hU p hp hY => ?_⟩
    · simp only [map_one, inv_one, mul_one, h0, h1]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
      exact supp_mul (mono (hs₁ a ha)) (hl y)
    · have key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p))
          = H₀ (cmp w p) * W g := by
        intro g hg
        rw [comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]
        · intro ν hν y
          beta_reduce
          rw [map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc,
            hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]
          rfl
        · intro y u hu
          beta_reduce
          rw [map_mul, ← mul_assoc]
          exact hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)
      set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'
      have e0 : cmp w p' = 1 := by
        rw [hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _,
          mul_inv_cancel]
      have e1 : ∀ v, v ≠ w → cmp v p' = cmp v p := fun v hv => by
        rw [hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _,
          inv_one, mul_one]
      have hS : SuppIn S p' := fun v hv => by
        by_cases h : v = w
        · subst h; exact e0
        · rw [e1 v h]
          exact hp v fun h' => (Finset.mem_insert.1 h').elim h hv
      have hY' : IsY (n - 1) p'.val := isY_of_cmp fun v => by
        by_cases h : v = w
        · subst h; rw [e0]; exact isY_one
        · rw [e1 v h]; exact isY_map _ hY
      have ep : p = p' * locGL E n w (cmp w p) := by rw [hp', inv_mul_cancel_right]
      have hI := hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg))
        (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'
      rw [hc, mul_assoc, ← hI]
      unfold comb at key ⊢
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x hx => ?_
      have e2 : p * x = p' * x * locGL E n w (cmp w p) := by
        rw [mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]
      rw [e2, key _ (supp_mul hS (hs₁ x hx))]
      ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

theorem UpperTheory.V.Af.StrongMultiplicityOne.orthStep :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.OrthStep := by
  classical
  intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n) := by
    set_option synthInstance.maxHeartbeats 400000 in
      infer_instance
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ = ν at *
  have : SFinite ν := sfinite_of_finite ν
  have : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  have : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g) := fun g γ x => by
    show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)
    rw [mul_assoc]
    exact hl γ _
  have hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x := fun x γ g => by
    show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x
    unfold chart
    split_ifs with hx
    · exact hr _ γ g
    · rfl
  let F : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n → ℂ := fun z =>
    CuspidalSpectrum.cuspQuot (hF z.2) z.1
  have hFmk : ∀ (y : Reduction.normOneGL (K := E) (n := n)) x,
      F (RightCosetSpace.mk (Reduction.rationalGLOne (K := E) (n := n)) y, x) = chart f y.1 x := fun _ _ => rfl
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hFb : ∀ z, ‖F z‖ ≤ C := by
    rintro ⟨q, x⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    unfold chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0 := by
    intro q x hx
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    exact dif_neg hx
  have hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)))) ×ˢ invSet E n) :=
    isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet
  have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
    rintro ⟨q, x⟩ ⟨-, hx⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne (K := E) (n := n))).prodMap
      (IsOpenQuotientMap.id (X := Lie E n))
    refine ContinuousAt.continuousWithinAt ?_
    refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
    have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
      (hcc E n f hf).1.continuousAt ((isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
    have h2 : Continuous fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact ContinuousAt.comp (f := fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n))
      (x := (y, x)) h1 h2.continuousAt
  have hFm : Measurable F := by
    have hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ :=
      (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩
    have := hFc.measurable_piecewise hc hopen.measurableSet
    rwa [Set.piecewise_same] at this
  have hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n =>
      (a z.1 * F z) * β z.2)
      (ν.prod volume) := by
    have hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n => β z.2)
        (ν.prod volume) :=
      (β.integrable (μ := volume)).comp_snd _
    refine hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))
  have e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x := by
    intro q
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]
    simp only [hFmk, mul_assoc]
  have e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0 := by
    intro x
    rw [integral_mul_const]
    by_cases hx : x ∈ invSet E n
    · have hx' : IsUnit (Matrix.of x) := hx
      have e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q := by
        intro q
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [hFmk, CuspidalSpectrum.cuspQuot_mk]
        exact dif_pos hx'
      simp only [e]
      rw [h0, zero_mul]
    · simp [hF0 _ x hx]
  simp only [e1]
  rw [integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]
  simp only [e2, integral_zero]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.CenSame := by
  intro hC hS E _ _ n U U' hU hs hc φ' hφ' s g'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n U U' hs φ φ'
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 φ.2.1.continuous φ'.2.1.continuous φ.2.1.isLeftInvariant φ'.2.1.isLeftInvariant
    (fun w hw => ⟨(hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  obtain ⟨z, hz⟩ : ∃ z : (Ad E)ˣ, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) z :=
    ⟨_, Units.ext rfl⟩
  have e1 := e z g g'
  rw [← hz, apply_mul_centralSection_of_mem (hc hφ)] at e1
  rw [Reduction.centralSection_mul_comm]
  exact (mul_left_cancel₀ hg e1).symm
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem cc_infGL (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Cinf F → Ad F) := (GlobalTheory.CuspRep.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Af.StrongMultiplicityOne.chartCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Cinf E) :=
      fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit
    have hu : Continuous u := cc_unit E n u (continuous_snd.comp continuous_subtype_val)
    have e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) =
        fun z => f (z.1.1 * infGL E n (u z)) := by
      funext z
      have h : IsUnit (Matrix.of z.1.2) := z.2.2
      change chart f z.1.1 z.1.2 = _
      rw [chart, dite_eq_left h]
    rw [e]
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))
  refine ⟨h1, fun g => ?_⟩
  classical
  have h2 : ContinuousOn (chart f g) (invSet E n) :=
    h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn
      fun x hx => ⟨Set.mem_univ _, hx⟩
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const GlobalTheory.CuspRep.isOpen_invSet.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ invSet E n
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, chart, dite_eq_right (show ¬ IsUnit (Matrix.of x) from hx)]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.proj :
    UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Proj := by
  intro hE E _ _ _ n U U' C sU sU' sC h0 hne hle hs
  have sup : ∀ T : Module.End ℂ (cuspForms E n), (∀ φ ∈ U, T φ ∈ U) → (∀ φ ∈ U', T φ ∈ U') →
      ∀ φ ∈ U ⊔ U', T φ ∈ U ⊔ U' := fun T h h' φ hφ => by
    obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hφ
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h u hu) (h' x hx)
  refine ⟨C ⊓ (U ⊔ U'), inf_le_left, fun e => hne (eq_bot_iff.2 fun x hx => ?_),
    ⟨fun X φ h => ⟨sC.ρ X φ h.1, sup _ (sU.ρ X) (sU'.ρ X) φ h.2⟩,
      fun X φ h => ⟨sC.σ X φ h.1, sup _ (sU.σ X) (sU'.σ X) φ h.2⟩,
      fun X φ h => ⟨sC.τ X φ h.1, sup _ (sU.τ X) (sU'.τ X) φ h.2⟩⟩,
    hs.mono fun w ⟨B, h1, h2⟩ => ⟨B, h1, fun c hc hK => ?_⟩⟩
  · obtain ⟨u, hu, c, hc, e'⟩ := Submodule.mem_sup.1 (hle hx)
    have h1 : c ∈ C ⊓ (U ⊔ U') := ⟨hc, by
      rw [show c = -u + x by rw [← e']; abel]
      exact Submodule.add_mem_sup (U.neg_mem hu) hx⟩
    rw [e, Submodule.mem_bot] at h1
    rw [h1, add_zero] at e'
    rw [← h0]
    exact ⟨e' ▸ hu, hx⟩
  · obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.1 hc.2
    have ev : ∀ (φ : cuspForms E n) k g, (finRepCusp E n k φ).1 g = φ.1 (g * finGL E n k) := fun φ k g => by
      rw [← Fb.finEmb_eq]
      rfl
    have key : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), finRepCusp E n (locGL E n w k) u = u ∧ finRepCusp E n (locGL E n w k) x = x := by
      intro k hk
      have e : finRepCusp E n (locGL E n w k) (u + x) = u + x :=
        Subtype.ext (funext fun g => (ev _ _ g).trans (hK g k hk))
      rw [map_add (f := _)] at e
      have e2 : finRepCusp E n (locGL E n w k) u - u = x - finRepCusp E n (locGL E n w k) x := by
        rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
      have m : finRepCusp E n (locGL E n w k) u - u ∈ U ⊓ U' :=
        ⟨U.sub_mem (sU.τ _ u hu) hu, e2 ▸ U'.sub_mem hx (sU'.τ _ x hx)⟩
      rw [h0, Submodule.mem_bot] at m
      exact ⟨sub_eq_zero.1 m, (sub_eq_zero.1 (e2.symm.trans m)).symm⟩
    have a := h1 (-u) (U.neg_mem hu) fun g k hk => by
      rw [← ev, map_neg, (key k hk).1]
    have b := h2 x hx fun g k hk => by rw [← ev, (key k hk).2]
    have e : (u + x).1 = x.1 - (-u).1 := by
      rw [← Submodule.coe_sub, sub_neg_eq_add, add_comm]
    rw [e]
    exact (hE E n w B _ b).2.2 _ a
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

theorem UpperTheory.V.Af.StrongMultiplicityOne.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.SetUp := by
  intro hP hL hN E _ _ n U U' hs φ φ'
  classical
  have lev : ∀ φ : cuspForms E n, ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := fun φ => by
    obtain ⟨V, hV⟩ := (hN E n φ).1
    obtain ⟨S, hS⟩ := hL E n V
    exact ⟨S, fun g k hk => hV g k (hS k hk)⟩
  obtain ⟨S₁, h₁⟩ := lev φ
  obtain ⟨S₂, h₂⟩ := lev φ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ Sat w B U ∧ Sat w B U' := fun w => by
    by_cases hw : w ∈ hf.toFinset
    · exact ⟨0, fun h => absurd hw h⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hg, B, hB⟩ := hw
      exact ⟨B, fun _ => ⟨hg, hB⟩⟩
  choose B hB using hB
  refine ⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h),
    fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_right
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.psiInf :
    UpperTheory.V.Af.StrongMultiplicityOne.PsiInf := by
  intro E _ _ _ x
  have h : GroundTheory.Global.adelicChar E (sInf E x) = 𝐞 (-TG.tr E x) := by
    have e : sInf E x = GroundTheory.Global.infiniteAdeleInl (GlobalTheory.CuspRep.infEq E x) := rfl
    rw [e, GroundTheory.Global.adelicChar_infiniteAdeleInl, TG.tr_apply, ← Finset.sum_neg_distrib,
      GroundTheory.Global.addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GroundTheory.Global.infiniteAdelicChar_apply_of_isComplex (IsTotallyComplex.isComplex w)]
    have e2 : InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.CuspRep.infEq E x w) = x w :=
      Cm.mixRing_snd x ⟨w, IsTotallyComplex.isComplex w⟩
    rw [e2]
  exact congrArg (fun z : Circle => (z : ℂ)) h
end
