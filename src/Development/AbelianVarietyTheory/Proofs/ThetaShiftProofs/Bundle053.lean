module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcTheta

theorem omegaStd_single_inl {g : ℕ} (u : Fin g ⊕ Fin g → ℤ) (k : Fin g) :
    omegaStd u (Pi.single (.inl k) 1) = -u (.inr k) := by
  simp [omegaStd, Pi.single_apply]

theorem mem_span_single_inl {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun k => (Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ)) '' (S : Set (Fin g))) ↔
      (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  first
  | exact @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | (apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff ..)

theorem exists_adapted {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (ω : LinearMap.BilinForm ℤ Λ) (hω : ∀ x, ω x x = 0) (hp : Function.Bijective ω) {g : ℕ}
    (hg : Module.finrank ℤ Λ = 2 * g) (K : Λ → Prop)
    (h1 : ∀ t, (∀ v, K v → ω t v = 0) → K t)
    (h2 : ∀ v, (∀ t, (∀ v', K v' → ω t v' = 0) → ω t v = 0) → K v) :
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ u v, ω (bas u) (bas v) = -omegaStd u v) ∧ (∀ u, K (bas u) ↔ ∀ k ∈ S, u (.inr k) = 0) ∧
      ∀ u, (∀ v', K v' → ω (bas u) v' = 0) ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  let I : Submodule ℤ Λ :=
    { carrier := {t | ∀ v, K v → ω t v = 0}
      add_mem' := fun ha hb v hv => by simp [ha v hv, hb v hv]
      zero_mem' := fun v _ => by simp
      smul_mem' := fun r x hx v hv => by simp [hx v hv] }
  have halt : ω.IsAlt := hω
  obtain ⟨g', bas, S, hs, hI, hr⟩ := GlobalTheory.exists_symplectic_coordinates_adapted halt hp (I := I)
    (fun k x hk hx v hv => by
      have := hx v hv
      simpa [hk] using this)
    (fun x hx y hy => hx y (h1 y hy)) (ε := -1) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  have hs' : ∀ u v, ω (bas u) (bas v) = -omegaStd u v := fun u v => by rw [hs]; ring
  have horth : ∀ u, bas u ∈ I ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := fun u => by
    rw [← mem_span_single_inl, hI]
    have : (fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g')) =
        bas.toLinearMap '' ((fun k => (Pi.single (Sum.inl k) 1 : Fin g' ⊕ Fin g' → ℤ)) '' (S : Set (Fin g'))) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span]
    exact Submodule.mem_map_equiv _ |>.trans (by simp)
  refine ⟨bas, S, hs', fun u => ⟨fun hu k hk => ?_, fun hu => h2 _ fun t ht => ?_⟩, horth⟩
  · have hm : bas (Pi.single (Sum.inl k) 1) ∈ I := by
      rw [hI]; exact Submodule.subset_span ⟨k, hk, rfl⟩
    have := hm _ hu
    rw [← halt.neg_eq, hs', omegaStd_single_inl] at this
    simpa using this
  · obtain ⟨t, rfl⟩ := bas.surjective t
    obtain ⟨e1, e2⟩ := (horth t).1 ht
    rw [hs', omegaStd, neg_eq_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [e1, hu k hk]
    · simp [e1, e2 k hk]

theorem isThetaFrameAt_of_isThetaFrame {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
    (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (h : IsThetaFrame L B y e θ) (b : Fin m → ℂ) (hb : b ∈ B) :
    ∃ fr, IsThetaFrameAt L (y b) (e b) (θ b) fr := by
  obtain ⟨fr, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun j z => fr j (b, z), fun j => ?_, fun j z => h2 j b z hb, fun j j' z => h3 j j' b z hb,
    fun j => h4 j b hb, h5 b hb⟩
  exact (h1 j).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn fun z hz => ⟨hb, hz⟩

theorem exists_isRigIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (L' : RigLB t'.G)
    (hL : L' = t'.PP) : ∃ w : LB.Iso L'.L (t.PP.L.pull m.φ), IsRigIso m.cm L' t.PP w := by
  subst hL
  obtain ⟨w, h1, h2, -⟩ := m.lin
  exact ⟨w, h1, h2⟩

theorem nonempty_thetaDat : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), IsTypeFn H Dw.p Dw.q ty → ∀ th : a.D₀.P.L.Sec, ThNZ th → Nonempty (ThetaDat Ha th) := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ th hth
  obtain ⟨nn, hN, hbe, -, hnn, hker, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let w₀ : ℂ := ((Ha.T + 1 : ℝ) : ℂ) * Complex.I
  have hw₀ : Ha.T < w₀.im := by simp [w₀]
  obtain ⟨-, hinj, hdisc, hsp, -⟩ := Ha.period w₀ hw₀
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.free_finite_finrank_of_discrete_span _ hinj hdisc hsp
  obtain ⟨bas, S, hs, hk, horth⟩ := exists_adapted (Fu.Di Ha.i).EF (Fu.Di Ha.i).alt (Fu.Di Ha.i).unimod hrk
    (fun v => Ha.y v = 0) hker (fun v hv => by
      by_contra hne
      have h0 := hv (nn v) fun v' hv' => by
        have := hbe v v'
        rw [hv', map_zero, neg_eq_zero] at this
        exact this
      have h1 := hbe v v
      have h2 := a.be_pos _ hne
      rw [h0] at h1
      omega)
  have hconst : ∀ w k, Ha.Pw w (bas (Pi.single (.inl k) 1)) = Ha.P₀ (bas (Pi.single (.inl k) 1)) := fun w k => by
    rw [Ha.Pw_eq, hN, hnn _ ((hk _).2 fun j _ => by simp), map_zero, smul_zero, add_zero]
  have hR := (GlobalTheory.RiemannRel.riemann_relations E H (Fu.Di Ha.i) g ty bas hs).1
  obtain ⟨h, τ₀, hh, -⟩ := hR _ (Ha.period w₀ hw₀)
  let τ : ℂ → Matrix (Fin g) (Fin g) ℂ := fun w =>
    h * Matrix.of fun i j => Ha.Pw w (bas (Pi.single (.inr j) 1)) i
  have hper : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1) := fun w k => by
    refine ⟨by rw [hconst, ← hconst w₀]; exact (hh k).1, ?_⟩
    rw [← Matrix.mulVec_mulVec, GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Ha.Pw w (bas (Pi.single (.inr j) 1))) k]
  have hpos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef := fun w hw => by
    obtain ⟨h', τ', -, -, e1, e2, hu⟩ := hR _ (Ha.period w hw)
    rw [(hu h (τ w) (hper w)).2]
    exact ⟨e1, e2⟩
  let B : Set (Fin 1 → ℂ) := {b | Ha.T < (b 0).im}
  have hBo : IsOpen B := isOpen_lt continuous_const (by fun_prop)
  have hBc : IsPreconnected B := by
    refine Convex.isPreconnected (?_ : Convex ℝ B)
    exact (convex_halfSpace_im_gt Ha.T).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)
  obtain ⟨c₁, c₂, hc₁, hc₂, hfr⟩ := Fu.theta Ha.i 1 B (fun b => Ha.Pw (b 0)) bas (-1) (fun _ => h) (fun b => τ (b 0))
    hBo hBc ⟨fun b hb => Ha.period _ hb, fun x => by
      simp only [Ha.Pw_eq]
      fun_prop⟩ (fun u v => by rw [hs]; simp) (fun b hb => ⟨(hpos _ hb).2, hper _⟩)
  have hframe : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w))
      (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr := fun w hw =>
    isThetaFrameAt_of_isThetaFrame _ _ _ _ _ hfr (fun _ => w) hw
  obtain ⟨⟨θ, ⟨s, fam, -, hex, hfam, -⟩, -⟩, -⟩ := GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W th hth
  obtain ⟨w₂, hw₂⟩ := exists_isRigIso W.m W.P.U.LG W.P.bundle
  obtain ⟨w₁, hw₁⟩ := exists_isRigIso Y.m _ rfl
  obtain ⟨w₃, hw₃⟩ := exists_isRigIso Y.m0.toSABMap _ rfl
  have hne : ∃ j, th.f j ≠ 0 := by
    obtain ⟨x, -, hx⟩ := hth (IsLocalRing.closedPoint ℂ)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj
  obtain ⟨fr₀, hfr₀⟩ := hframe w₀ hw₀
  obtain ⟨κ, hκ, hS, hB, -⟩ := Ha.theta th s fam bas S h τ c₁ c₂ w₂ w₁ w₃ hne hex hfam hs hk hper hc₁ hc₂
    hw₂ hw₁ hw₃ ⟨w₀, fr₀, hw₀, hfr₀⟩
  exact ⟨⟨bas, S, h, τ, c₁, c₂, κ, hs, hk, horth, hper, hpos, hc₁, hc₂, hframe, hκ, hS, hB⟩⟩

end GlobalTheory.ArcTheta
end

section



noncomputable section

namespace GlobalTheory.ArcQ.DiscInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem flat_of_injective {A V : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing V] [IsDomain V]
    (f : A →+* V) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).2 hf
  show Module.Flat A V
  infer_instance

theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {G : SAB H S'} {t' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap G t f) (n : SABMap t' G g) (k : SABMap t' t h) (hb : h = g ≫ f)
    (hφ : k.φ = n.φ ≫ m.φ) (θ : LB.Sec t.PP.L) (w : LB.Iso t'.PP.L (t.PP.L.pull k.φ)) (σ : LB.Sec t'.PP.L)
    (θ2 : LB.Sec (t.PP.L.pull k.φ)) (r : RigIso k w) (hi : IsoMaps w σ θ2) (hp : PullSec k.φ θ θ2) :
    ∃ (θ' : LB.Sec G.PP.L) (w' : LB.Iso t'.PP.L (G.PP.L.pull n.φ)),
      (∀ s : S', (∃ x : t.G.left, t.G.hom x = f s ∧ x ∈ Out.nonzeroLocus θ) →
        ∃ x : G.G.left, G.G.hom x = s ∧ x ∈ Out.nonzeroLocus θ') ∧
      RigIso n w' ∧ IsoMaps w' σ (thfPull G.PP.L n.φ θ') := by
  obtain ⟨w0, g0, r0, -⟩ := m.lin
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ
  have he : k.cm.e = n.cm.e ≫ m.cm.e := by rw [k.base, n.base, m.base, hb]
  obtain ⟨w', r', tri⟩ := GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r
  refine ⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩
  · rintro s ⟨z, hz, hz'⟩
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z s hz
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have u₁ : IsUnit (gs m.φ y _ (θ.f j)) := by rw [gs_stalkMap m.φ y _ hj]; exact u.map _
    have e := hθ' _ (𝟙 _) y j i hj hi
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · have hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (n.φ y))
    have pt : k.φ y = m.φ (n.φ y) := congrArg (fun q => q y) hφ
    have hj' : k.φ y ∈ t.PP.L.U j := pt ▸ hj
    have e1 := hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'
    have e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k') := by
      have hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k' := ⟨mem_pull.2 hj', hy.2⟩
      have le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      have a := congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')
      refine (gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_
      rw [← hp (fun _ => j) le]
      exact (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2
    have e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ := by rw [Category.assoc, hφ]
    rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
    refine (gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.ArcQ.DiscInt

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames


open DiscInt in
theorem integral_of_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ ρ e th hB hth hPI T io ev hinj hρ
  letI := io.toAlgebra
  intro y hy
  obtain ⟨z, t', m1, k, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, p2, hg⟩ := hy
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G W.t (spMap ev)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ev) W.t
    exact ⟨_, ⟨m⟩⟩
  have hb := sp_comp ev (algebraMap T.V T.Fr)
  obtain ⟨n, hn⟩ : ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
    have key : ∀ (g : Sp T.Fr ⟶ _) (k : SABMap t' W.t g), g = spMap (algebraMap T.V T.Fr) ≫ spMap ev →
        ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
      intro g k hg
      subst hg
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m k
    exact key _ k hb
  obtain ⟨u, hu1, hu2⟩ :=
    GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB
      T.V ev (flat_of_injective _ hinj) G m
  have eig : ∀ (τ : E →+* ℂ) (w : epsR T.V ⟶ G.G), IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left =
      spMap (epsScaleR (ev (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left := fun τ w =>
    ⟨fun h x => h x _ (hρ τ x).symm, fun h x s hs => by
      obtain rfl : s = ev (PowerSeries.C (R := A) (ρ τ x)) := IsFractionRing.injective T.V T.Fr (hs.trans (hρ τ x))
      exact h x⟩
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m n k hb hn θ w2 σ θ2 r2 i2 p2
  refine ⟨G, t', m1, n, ⟨u, fun τ i => (isTan_iff _).2 ((hu2 τ).1 i).1, fun τ i => (eig τ _).2 ((hu2 τ).1 i).2,
    fun τ w h1 h2 => (hu2 τ).2 w ((isTan_iff _).1 h1) ((eig τ w).1 h2), fun τ i => ?_⟩, θ',
    GlobalTheory.T.polarisation_section_generates_of_special_fibre hL hL2 E H Dw l Xo c T G t' y.x m1 n θ'
      (hnz _ (GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ (Or.inr hPI) _).2),
    w1, w', σ, s1, thfPull G.PP.L n.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨v, p, h1, h2, h3, pb⟩ := hu τ i
  obtain ⟨v', h1', h3'⟩ := hu1 τ i
  obtain rfl : v = v' := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ i)).1.unique h1 h1'
  refine ⟨p, h2, ?_⟩
  apply m.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact (congrArg _ hn.symm).trans (h3.trans (by rw [dual_comp, Category.assoc]; exact congrArg _ h3'.symm))
  · have ub : (u τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (u τ i)
    rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, pb]
    exact ((congrArg _ ub).trans (dual_alg _)).symm

end GlobalTheory.ArcQ
end
end
