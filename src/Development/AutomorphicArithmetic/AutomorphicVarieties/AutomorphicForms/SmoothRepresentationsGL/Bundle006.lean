module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
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
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

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

theorem UpperTheory.V.Af.Smo.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.FinKir := by
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
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem comm_loc {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GA E n) (hg : cmp w (GeneralLinearGroup.map (pFin E) g) = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    g * finGL E n (locGL E n w y) = finGL E n (locGL E n w y) * g := by
  refine TR.ga_ext ?_ ?_
  · rw [map_mul, map_mul, TR.pInf_finGL, mul_one, one_mul]
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL]
    refine cmp_ext fun v => ?_
    rw [map_mul, map_mul]
    by_cases h : v = w
    · subst h
      rw [hg, mul_one, one_mul]
    · have : cmp v (locGL E n w y) = 1 := GlobalTheory.CuspRep.pLoc_locGL_of_ne h y
      rw [this, mul_one, one_mul]

theorem UpperTheory.V.Af.Smo.sphAll :
    UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.SphZero → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.SphAll := by
  intro hA hZ hE E _ _ _ n S B W hW hS hK p hp h0
  refine hA E n S (fun k => W (p * finGL E n k) = 0) (fun k hk => (hK p k hk).trans h0) ?_
  intro w hw k _ hk hP y
  have hc : cmp w (GeneralLinearGroup.map (pFin E) (p * finGL E n k)) = 1 := by
    rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL, hp w hw, hk, mul_one]
  obtain ⟨e1, e2, -, -⟩ := hE E n 0
  have hz := hZ E n w (psiL w) (hS w hw).1 (B w) _ ?_ ((hS w hw).2 (p * finGL E n k)) (by simpa using hP)
  · have := congrFun hz y
    simpa [mul_assoc] using this
  · intro ν hν g
    obtain ⟨a1, a2⟩ := e1 w ν hν
    obtain ⟨b1, b2⟩ := e2 _ a1
    have := hW _ b1 (p * finGL E n k * finGL E n (locGL E n w g))
    rw [b2, a2] at this
    show W _ = _
    rw [map_mul, map_mul, ← mul_assoc, comm_loc w _ hc ν, mul_assoc, this]
    rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

theorem UpperTheory.V.Af.Smo.orthStep :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.OrthStep := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
    have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
    generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ = ν at *
    have : SFinite ν := sfinite_of_finite ν
    have : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
    have : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
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
      isOpen_univ.prod TR.isOpen_invSet
    have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
      rintro ⟨q, x⟩ ⟨-, hx⟩
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne (K := E) (n := n))).prodMap
        (IsOpenQuotientMap.id (X := Lie E n))
      refine ContinuousAt.continuousWithinAt ?_
      refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
      have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
        (hcc E n f hf).1.continuousAt ((isOpen_univ.prod TR.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
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
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem cc_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Rinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Af.Smo.chartCont :
    UpperTheory.V.Af.Smo.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Rinf E) :=
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
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const TR.isOpen_invSet.measurableSet
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
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lev (hL : LevelS) {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (π : CuspSub E n)
    (φ : TR.Sm E n) (hφ : φ ∈ π.V) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := by
  let V : OpenSubgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | TR.finRep E n k φ = φ}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      isOpen' := (π.cusp φ hφ).1.level }
  obtain ⟨S, hS⟩ := hL E n V
  refine ⟨S, fun g k hk => ?_⟩
  have h : TR.finRep E n k φ = φ := hS k hk
  exact congrArg (fun ψ : TR.Sm E n => ψ.1 g) h

private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

theorem UpperTheory.V.Af.Smo.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.Smo.SetUp := by
  intro hP hL E _ _ _ n π π' hs φ hφ φ' hφ'
  classical
  obtain ⟨S₁, h₁⟩ := lev hL π φ hφ
  obtain ⟨S₂, h₂⟩ := lev hL π' φ' hφ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ π.HasSat w B ∧ π'.HasSat w B := fun w => by
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
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.betaSch :
    UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch := by
  intro hP V M _ _ _ _ _ _ _ _ B hB K
  set Φ : V × M → V × M := fun z => (z.1, z.2 - B z.1 z.2) with hΦdef
  have hΦ : Function.HasTemperateGrowth Φ := by
    let B2 : V →L[ℝ] M →L[ℝ] V × M :=
      (ContinuousLinearMap.compL ℝ M M (V × M) (ContinuousLinearMap.inr ℝ V M)).comp B
    have h1 : Function.HasTemperateGrowth (fun z : V × M => B2 z.1 z.2) :=
      B2.bilinear_hasTemperateGrowth (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
        (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
    have h2 := (ContinuousLinearMap.id ℝ (V × M)).hasTemperateGrowth.add h1.neg
    convert h2 using 1
    funext z
    ext <;> simp [Φ, B2, sub_eq_add_neg]
  have hbd : ∃ (k : ℕ) (C : ℝ), ∀ z : V × M, ‖z‖ ≤ C * (1 + ‖Φ z‖) ^ k := by
    refine ⟨2, 1 + ‖B‖, fun z => ?_⟩
    obtain ⟨u, x⟩ := z
    set t := ‖Φ (u, x)‖ with ht
    have hu : ‖u‖ ≤ t := norm_fst_le (Φ (u, x))
    have hy : ‖x - B u x‖ ≤ t := norm_snd_le (Φ (u, x))
    have hx : x = (x - B u x) + B u (x - B u x) := by
      rw [map_sub, hB, sub_zero, sub_add_cancel]
    have hBu : ‖B u (x - B u x)‖ ≤ ‖B‖ * ‖u‖ * ‖x - B u x‖ := B.le_opNorm₂ _ _
    have hxle : ‖x‖ ≤ t + ‖B‖ * t * t := by
      calc ‖x‖ = ‖(x - B u x) + B u (x - B u x)‖ := by rw [← hx]
        _ ≤ ‖x - B u x‖ + ‖B u (x - B u x)‖ := norm_add_le _ _
        _ ≤ t + ‖B‖ * t * t := by
          have := norm_nonneg B
          have := norm_nonneg u
          have := norm_nonneg (x - B u x)
          nlinarith [mul_le_mul hu hy (norm_nonneg _) (le_trans (norm_nonneg _) hu)]
    have ht0 : 0 ≤ t := norm_nonneg _
    have hB0 := norm_nonneg B
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  let K' : 𝓢(V × M, ℂ) := SchwartzMap.compCLM ℂ hΦ hbd K
  obtain ⟨L, hL⟩ := hP V M K'
  have hι : Function.HasTemperateGrowth (fun x : M => ((0 : V), x)) := by
    convert (ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth using 1
    funext x
    rfl
  have hιb : ∃ (k : ℕ) (C : ℝ), ∀ x : M, ‖x‖ ≤ C * (1 + ‖((0 : V), x)‖) ^ k := by
    refine ⟨1, 1, fun x => ?_⟩
    have h := norm_snd_le ((0 : V), x)
    simp only [pow_one, one_mul]
    linarith
  refine ⟨K', SchwartzMap.compCLM ℂ hι hιb L, fun u x => rfl, fun x => ?_⟩
  change L ((0 : V), x) = _
  rw [hL]
  simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
end
