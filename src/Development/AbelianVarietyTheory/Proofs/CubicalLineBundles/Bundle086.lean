module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementS
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetricDataCmPointComplexEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle084
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle083
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHermFormCurve
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_metricData_cmPoint_complexEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (σ : z.K →+* ℂ) (yσ : FrPt Xo c (CAt (σ.comp (algebraMap c.F z.K)))), FrMap (embAlg σ) z.y yσ → ∃ Hm : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) ℂ, Hm.PosDef ∧ z.LamL.n σ = Real.sqrt Hm.det.re ∧ (∀ j, ReciprocityTheory.MultiplicativeHeights.hq Hm (ReciprocityTheory.MultiplicativeHeights.embVec σ (z.U j)) ≤ (La * (z.ℓ j).n σ) ^ 2) ∧ IsMetric yσ (z.Tl.n σ ^ 2) (gramBlock z.e z.U Hm σ) := by
  first | exact @GlobalTheory.LamT.CMMetric.exists_isMetric | exact GlobalTheory.LamT.CMMetric.exists_isMetric | (intros; apply GlobalTheory.LamT.CMMetric.exists_isMetric <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocGen

theorem fibre_ne_of_generates {R : Type} [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (θ : P.L.Sec)
    (h : ∀ σ : P.L.Sec, ∃ c : ∀ i, Γ(P.A.left, P.L.U i), ∀ i, σ.f i = c i * θ.f i) (s : Sp R) :
    ∃ q : P.A.left, P.A.hom q = s ∧ q ∈ Out.nonzeroLocus θ := by
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : IsPullback (𝟙 P.A.left) P.A.hom P.A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨th, hth⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨q, hq, hz⟩ := hth s
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  obtain ⟨c, hc⟩ := h ⟨fun j => (P.A.left.presheaf.map (homOfLE (fun y hy => mem_pull.2 hy :
      P.L.U j ≤ (P.L.pull (𝟙 P.A.left)).U (fun _ => j))).op).hom (th.f fun _ => j), fun j j' => fn_ext fun y hy => by
    have h₁ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j) := mem_pull.2 hy.1
    have h₂ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j') := mem_pull.2 hy.2
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat th (𝟙 _) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans ?_)
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
    rw [gm_pull_g P.L (𝟙 _) (𝟙 _) y _ _ h₁ h₂, Category.comp_id]⟩
  have hk' : q ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  refine ⟨q, hq, (mem_nonzeroLocus _ _).2 ⟨_, hk', ?_⟩⟩
  have e := congrArg (gs (𝟙 _) q _) (hc (k PUnit.unit))
  rw [gs_mul _ q _ hk'] at e
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_res (𝟙 _) q _ hk' _).symm.trans e)).mp u)

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    {v : Fin k → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin n => v (i.cast e) := by
  subst e; exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    (B : Matrix (Fin k) (Fin k) R) {v w : Fin k → (epsR R ⟶ G)} (h : ∀ i, IsLieComb (B i) v (w i)) (i : Fin n) :
    IsLieComb ((Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)) i) (fun i : Fin n => v (i.cast e))
      (w (i.cast e)) := by
  subst e; exact h i

theorem det_cast {R : Type} [CommRing R] {n k : ℕ} (e : n = k) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)).det = B.det := by
  subst e; rfl

theorem eps_sq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem stalk_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {θ : L.Sec} {θ' : (L.pull F).Sec} {σ : L'.Sec} (h : IsoMaps w σ θ') (hθ : PullSec F θ θ')
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  rw [← (TieCalc.isoMaps_iff w σ θ').1 h Z r z j k hj hk, hθ (fun _ => j) le, gs_appLE F _ _ le r z (mem_pull.2 hj)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem keyPB_of_sabMap {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {T : PAT H (Sp R)} {T' : PAT H (Sp R')}
    (m : SABMap T'.t T.t (spMap f)) {w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ)} (hw : RigIso m w) (hg : T'.g = T.g)
    {g₀ th hth v hv g₀' th' hth' v' hv'}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.t.G.left) (z : Z) j k, m.φ (r z) ∈ T.t.PP.L.U j → r z ∈ T'.t.PP.L.U k →
      gs (r ≫ m.φ) z _ (LB.Sec.f th j) = (gw w r z j k).val * gs r z _ (LB.Sec.f th' k))
    (hl : ∀ i, (v' i).left ≫ m.φ = spMap (Chart.dualMapR f) ≫ (v (i.cast hg)).left) :
    KeyPB ⟨T'.pol, g₀', T'.t.PP.rig, T'.t.PP.rigGen, th', hth', v', hv'⟩
      ⟨T.pol, g₀, T.t.PP.rig, T.t.PP.rigGen, th, hth, v, hv⟩ f := by
  have he : eSec T'.t.G ≫ m.φ = spMap f ≫ eSec T.t.G := PolBaseChange.eSec_comm m.cart
  have hr := (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm T.t.PP.L) (fun _ => rfl)).1 hw.2
  rw [m.base] at hr
  refine ⟨m.φ, he, w, hg, Chart.dualMapR f, m.cart, hw.1,
    (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig _ _ (rigPull_le m.φ _ he T.t.PP.L) (fun _ => rfl)).2 hr,
    KeyPow.appLE_eq_of_stalk _ th th' (hs _ (𝟙 _)), fun a => ?_, ?_, hl⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem eq_mul_of_secTie {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x x₀ : Sp S ⟶ Xo.X}
    {x₁ x₂ : Sp S' ⟶ Xo.X} {t : SAB H (Sp S)} {t' : SAB H (Sp S')} {m : SABMap t Xo.univ.t x}
    {m' : SABMap t' Xo.univ.t (spMap φ ≫ x)} {n : SABMap t' t (spMap φ)} (hφ : m'.φ = n.φ ≫ m.φ)
    {th : LB.Sec t.PP.L} {s₀ : LB.Sec (PPx x₀)} {s₁ : LB.Sec (PPx x₁)} {s₂ : LB.Sec (PPx x₂)} {a : S'}
    (e₀ : x₀ = x) (e₁ : x₁ = spMap φ ≫ x₀) (e₂ : x₂ = x₁) (h₀ : SecTie m th s₀) (b₁ : SecBC φ 1 x₀ x₁ s₀ s₁)
    (b₂ : SecBC (RingHom.id S') a x₁ x₂ s₁ s₂) {w : LB.Iso t'.PP.L (t.PP.L.pull n.φ)} (hw : RigIso n w)
    {th' σ : LB.Sec t'.PP.L}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j k, n.φ (r z) ∈ t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ n.φ) z _ (th.f j) = (gw w r z j k).val * gs r z _ (th'.f k))
    (h₂ : SecTie m' σ s₂) : ∀ i, σ.f i = constFn t'.G.hom _ a * th'.f i := by
  subst e₀ e₁
  have h₁ : SecTie m' th' s₁ :=
    (TieCalc.secTie_baseChange m h₀ φ m' n s₁ w (thfPull _ n.φ th) th' rfl hφ b₁ hw (fun _ _ => rfl)).2
      ((TieCalc.isoMaps_iff w _ _).2 fun Z r z j k hj hk =>
        (gs_appLE n.φ _ _ _ r z (mem_pull.2 hj) _).trans (hs Z r z j k hj hk))
  exact ((TieCalc.secTie_calc E H Dw l Xo S' _ t' m' th' s₁ h₁).1 a x₂ s₂ σ e₂ b₂).1 h₂

theorem integral_generator_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hT φ yT y' g a hφ hmap hchg hint ca hca
  obtain ⟨hobj, -, -, hx, htie, -⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := hobj
  obtain ⟨A, hA, hdet⟩ := hmod p
  obtain ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, hσ⟩ := hint
  have hvV : ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Chart.dualMapR iK) ≫ wK.left ≫ z.m'.φ := by
    obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩ := hA
    have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have exists_restrict_ringHom {R K V F : Type} [CommRing R] [CommRing K] [CommRing V] [CommRing F]
        (a : R →+* K) (b : V →+* F) (hb : Function.Injective b) (i : K →+* F)
        (h : ∀ r : R, i (a r) ∈ Set.range b) : ∃ ψ : R →+* V, b.comp ψ = i.comp a := by
      choose ψ hψ using h
      refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;> simp [hψ]
    obtain ⟨ψ, hψ⟩ := exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK
      (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))
    have hρψ : M.ρ = ψ.comp ρ := by
      refine RingHom.ext fun x => hinj ?_
      have h₁ := RingHom.congr_fun M.hρ x
      have h₂ := RingHom.congr_fun hψ (ρ x)
      have h₃ := RingHom.congr_fun hρ x
      simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
      rw [h₁, h₂, h₃]
    have hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR := hfib
    have e : spMap M.ρ = spMap ψ ≫ spMap ρ := by rw [hρψ]; exact spMap_comp ρ ψ
    have hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ := M.n.cart
    have w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ := by rw [hn.1.w, e, Category.assoc]
    have hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w) :=
      IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)
    have := xR.P.isAb.comm
    obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis
    have hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm) := by
      rintro k rfl
      exact hb
    refine ⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩
    obtain ⟨wK, hw, hw'⟩ := hv k
    refine ⟨wK, hw, ?_⟩
    have ed : (Chart.dualMapR (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) =
        (Chart.dualMapR iK).comp (Chart.dualMapR (algebraMap R z.K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ x.fst
      have h₂ := RingHom.congr_fun hψ x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Chart.dualMapR, Chart.dualMapR] using h₁
      · simp only [Chart.dualMapR, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        exact h₂
    have es : spMap (Chart.dualMapR (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) =
        spMap (Chart.dualMapR iK) ≫ spMap (Chart.dualMapR (algebraMap R z.K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ =
        spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR := by
      rw [← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]
    exact (congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <|
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)
  obtain ⟨vV, bV, hV⟩ := hvV
  obtain ⟨g1, -, w1, r1⟩ := (pat_pullback E H _ _ iK z.Φ.T).2 M.t' M.n' inferInstance
  obtain ⟨g2, -⟩ := (pat_pullback E H _ _ (algebraMap T.V T.Fr) M.G).2 M.t' M.m2 inferInstance
  have g3 : M.G.g = z.Φ.T.g := g2.symm.trans g1
  obtain ⟨th', hth'⟩ := sec_pull_down ((isGen_iff _).1 r1.1) z.Φ.T.t.PP.isLB M.t'.t.PP.isLB z.Φ.th
  have nz' := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hth' M.n'.cart.1 z.Φ.th_ne
  have nzθ := fibre_ne_of_generates M.G.pol θ fun τ => (hθ τ).exists.elim fun b hb => ⟨_, hb⟩
  have hσθ := stalk_of_isoMaps i2 p2
  have nzσ := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hσθ M.m2.cart.1 nzθ
  obtain ⟨v0, b0, h0⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ iK _ _ _ M.n'.cart z.Φ.T.ab.smooth _ z.Φ.v z.Φ.basis
  obtain ⟨v1, b1, h1⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ (algebraMap T.V T.Fr) _ _ _ M.m2.cart M.G.ab.smooth _ vV bV
  have hc : ∀ k, IsLieComb (iK.mapMatrix A k) v0 (v1 k) := fun k => by
    show IsLieComb (fun j => iK (A k j)) v0 (v1 k)
    obtain ⟨wK, hw, hw'⟩ := hV k
    refine Chart.comb_baseChange iK M.n'.cart hw h0 (z.m'.cart.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← M.h2, ← Category.assoc, h1, Category.assoc]
      exact hw'
    · rw [Category.assoc, Category.assoc, M.n'.cart.1.w, ← Category.assoc, Over.w, Over.w, eps_sq]
  have hσa : ∀ i, σ.f i = constFn M.t'.t.G.hom _ a * th'.f i := by
    obtain ⟨e₁, -, pm, ps, pf, hp⟩ := hmap
    rw [hφ] at e₁ pf
    refine eq_mul_of_secTie iK M.h1 hx e₁ hchg.1 htie ⟨pm, ps, pf, fun i h => ?_⟩ hchg.2.2 r1 hth' hσ
    rw [SecCalc.scal_one' z.y.x i, _root_.one_mul]
    exact hp i h
  have gp : 1 ≤ M.t'.g := g1 ▸ z.Φ.g_pos
  let x' : KeyIn T.Fr := ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, th', nz', _, isLieBasis_cast g1 b0⟩
  let xR : KeyIn T.V := ⟨M.G.pol, gp.trans g2.le, M.G.t.PP.rig, M.G.t.PP.rigGen, θ, nzθ, _, isLieBasis_cast g3 bV⟩
  have k1 : KeyPB x' z.Φ.key iK := keyPB_of_sabMap M.n' r1 g1 hth' fun i => h0 _
  have k2 : KeyPB ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, σ, nzσ, _, isLieBasis_cast g1 b1⟩ xR
      (algebraMap T.V T.Fr) := keyPB_of_sabMap M.m2 r2 g2 hσθ fun i => h1 _
  have k3 : KeyIntegral T.V x' a (iK A.det) :=
    ⟨σ, nzσ, _, isLieBasis_cast g1 b1, Matrix.of fun i j => iK.mapMatrix A (i.cast g1) (j.cast g1), xR, hσa,
      isLieComb_cast g1 (iK.mapMatrix A) hc, (det_cast g1 _).trans (RingHom.map_det iK A).symm, k2⟩
  exact KeyVal.integral_section_unit z.K z.Φ.key z.Tl z.LamL p (hloc p) T.V T.Fr iK x' a (iK A.det) ca A.det 1 hT
    k1 k3 hdet (by rw [Units.val_one, map_one, _root_.mul_one]) hca

end GlobalTheory.LamT.LocGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.ExObj

theorem additive_ext {V L M : Type} [AddCommGroup V] [Module ℂ V] [Group M] {P : L → V}
    (hP : Submodule.span ℝ (Set.range P) = ⊤) {u v : V → M} (hu : ∀ z w, u (z + w) = u z * u w)
    (hv : ∀ z w, v (z + w) = v z * v w) (h : ∀ a (c : ℂ), u (c • P a) = v (c • P a)) (z : V) : u z = v z := by
  have u0 : u 0 = 1 := by simpa using hu 0 0
  have v0 : v 0 = 1 := by simpa using hv 0 0
  have key : ∀ c : ℂ, u (c • z) = v (c • z) := by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
    | zero => intro c; rw [smul_zero, u0, v0]
    | add x y _ _ hx hy => intro c; rw [smul_add, hu, hv, hx, hy]
    | smul r x _ hx => intro c; rw [← Complex.coe_smul, smul_smul]; exact hx _
  simpa using key 1

theorem exists_sum {J V L : Type} [Fintype J] [AddCommGroup V] [Module ℂ V] {W : J → Type} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] (F : ∀ j, W j →ₗ[ℂ] V) {P : L → V} (hP : Submodule.span ℝ (Set.range P) = ⊤) {n : ℕ}
    (hn : 0 < n) (h : ∀ a, ∃ x : ∀ j, W j, n • P a = ∑ j, F j (x j)) (z : V) : ∃ x : ∀ j, W j, z = ∑ j, F j (x j) := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
  have sm : ∀ (c : ℂ) (y : V), (∃ x : ∀ j, W j, y = ∑ j, F j (x j)) → ∃ x : ∀ j, W j, c • y = ∑ j, F j (x j) := by
    rintro c _ ⟨x, rfl⟩
    exact ⟨fun j => c • x j, by simp [Finset.smul_sum]⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := sm (n : ℂ)⁻¹ _ (h a)
    rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul] at this
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp [Finset.sum_add_distrib]⟩
  | smul r x _ hx => rw [← Complex.coe_smul]; exact sm _ _ hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_ten_exp (hT : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R] [IsNoetherianRing R] {ω : R}
    (C : Ell H R ω) (σ : R →+* ℂ) {ω' : ℂ} (C' : Ell H ℂ ω') (π : C'.P.A.left ⟶ C.P.A.left)
    (u₀ : HolUnif C'.P.A C'.P.L C'.P.g) (c : ℂ) (D : Datum H) (ε : ℤˣ) (hm : EllMap C' C σ π) (hc : c ≠ 0)
    (hu : PureType.IsQuadLattice u₀.Λ H.d c) (hε : 0 < ((ε : ℤ) : ℝ) * ω'.im)
    (hD : (D.q = 0 ∧ 2 * ω' - 1 = H.rt0) ∨ (D.p = 0 ∧ 2 * ω' - 1 = -H.rt0)) :
    ∃ (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (g : ℕ) (ty : Fin g → (E →+* ℂ))
      (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)),
      IsKForm D ε h ∧ IsTypeFn H D.p D.q ty ∧ IsExp T σ D ty P e ∧
      (∀ a (z : ℂ), (e (z • P a)).left = (u₀.ex (fun _ => c * z)).left ≫ π ≫ (t.ten.tmul a).left) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : D.La →+ V), (∀ a, f (H.w0 • a) = ω' • f a) →
        ∃ F : (Fin g → ℂ) →ₗ[ℂ] V, ∀ a, F (P a) = f a := by
  obtain ⟨h, hh, -⟩ := exists_kForm E H D ε
  have hpos := definite_datum_form_pos E H D ε (by
    rcases hD with ⟨a, b⟩ | ⟨a, b⟩
    · refine Or.inl ⟨a, ?_⟩
      have := congrArg Complex.im b
      simp at this
      rw [← this]; linarith
    · refine Or.inr ⟨a, ?_⟩
      have := congrArg Complex.im b
      simp at this
      rw [show H.rt0.im = -(2 * ω'.im) by linarith]; linarith)
  obtain ⟨T, ⟨t⟩, -⟩ := GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple hL E H R ω C D ε _ hh hpos
  obtain ⟨T', m, -⟩ := PAT.exists_pullback E H _ _ (spMap σ) T
  obtain ⟨t', ht'⟩ := isTen_baseChange E H R ω C D _ T t ℂ ω' C' σ π T' m hm
  obtain ⟨g, ty, P, e', hty, he', htie, hF⟩ := TenExp.exists_isExp_of_isTen hT hL E H ω' C' u₀ c D ε _ T' t' hc hu hε hh hD
  obtain ⟨e, he, hee⟩ := exists_isExp_push E H R σ T T' m D g ty P e' he'
  refine ⟨_, T, t, g, ty, P, e, hh, hty, he, fun a z => ?_, hF⟩
  rw [hee, htie, Over.comp_left, Category.assoc, ht']

theorem hasType_of_moduli {D : Datum H} {l : Level H} (Xo : Moduli D l) (K₁ : IntermediateField ℚ ℂ) [NumberField K₁]
    (hk : KA l ≤ K₁) (ρ : 𝓞 K₁) (hρ : ((ρ : K₁) : ℂ) = H.rt0) (B : SAB H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X)
    (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B (spMap (algebraMap (𝓞 K₁) K₁)))
    (hy : y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom) : HasType H B.act ρ D.p D.q := by
  refine (hasType_baseChange E H _ _ _ B t₀ m' ρ D.p D.q).2 (fun k _ β hβ => ?_) (fun k _ _ β _ τ => ?_)
  · exact ⟨IsFractionRing.lift hβ, RingHom.ext fun x => IsFractionRing.lift_algebraMap hβ x, RingHom.injective _⟩
  · have h := (Xo.univ.geom k (spMap β ≫ y) (β.comp (IntermediateField.inclusion hk).toRingHom) (by
      rw [Category.assoc, hy]; exact (Spec.map_comp _ _).symm)).1 τ
    have e : (β.comp (IntermediateField.inclusion hk).toRingHom) (baseKA l).ρ = β (algebraMap (𝓞 K₁) K₁ ρ) :=
      congrArg β (Subtype.ext hρ.symm)
    rw [e, ← LiePull.lieMult_pull _ _ _ _ _ y m.cm.F _ t₀.act m.cart m.act,
      ← LiePull.lieMult_pull _ _ _ _ _ y m.cm.F _ t₀.act m.cart m.act] at h
    exact h

theorem cmExists : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt →
    CMExistsSt := by
  intro h1 h2 hT hL hL2 hH hK E _ _ _ H D l Xo g ty FU i Pe hP Z k hkf
  obtain ⟨⟨k₀, hk₀, hconj⟩, hsplit, -⟩ := splits_basic E
  obtain ⟨K₁, inst, hk, ω, C, ε, h, B, y, t₀, m, m', ψ, ω', C', π, u₀, c, hkK, hy, hyu, hb⟩ :=
    GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre h1 h2 hT hL hL2 hH hK E H D l Xo g ty FU i Pe hP _ _ Z (k ⊔ k₀) inferInstance
  choose hω hε hh hψ hm hc hu htie using hb
  set σ : 𝓞 K₁ →+* ℂ := (algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁) with hσ
  have hσi : Function.Injective σ := (algebraMap K₁ ℂ).injective.comp (FaithfulSMul.algebraMap_injective _ _)
  have hσω : ∀ b, σ (2 * ω b - 1) = if b then H.rt0 else -H.rt0 := fun b => by
    rw [map_sub, map_mul, map_ofNat, map_one, (hm b).1, hω]
  choose h₁ T t gA tyA PA e hh₁ hty he hee hF using fun b : Bool =>
    exists_ten_exp hT hL (C b) σ (C' b) (π b) (u₀ b) (c b) (Z.D₁ b) (ε b) (hm b) (hc b) (hu b) (hε b) (by
      cases b
      · exact Or.inr ⟨Z.sigM.1, hω false⟩
      · exact Or.inl ⟨Z.sigP.2, hω true⟩)
  choose Φ hΦl hΦt hΦp using fun j : Fin D.p ⊕ Fin D.q =>
    exists_famLift E H _ _ (C j.isLeft) (Z.D₁ j.isLeft) (FU.Di i) (ε j.isLeft) (h₁ _) (h _) (T _) B (t _) _ (ψ j.isLeft)
      ((Z.f j).codRestrict _ (Z.pure j)) (Z.hh j) (hh₁ _) (hh _) (Z.form j) (hψ _)
  choose F hFP using fun j : Fin D.p ⊕ Fin D.q =>
    hF j.isLeft (Fin g → ℂ) (Pe.comp (Z.f j).toAddMonoidHom) (fun a => by
      show Pe (Z.f j (H.w0 • a)) = _ • Pe (Z.f j a)
      rw [map_smul, PureType.period_w0_smul hP (Z.pure j a), ← hω]
      congr 1
      ring)
  replace hFP : ∀ j a, F j (PA _ a) = Pe (Z.f j a) := hFP
  obtain ⟨κ', hκ'⟩ := LiePull.exists_pushEquiv m'.cart (Over.mk (spMap (algebraMap K₁ ℂ))) (spMap σ)
    (Spec.map_comp (CommRingCat.ofHom (algebraMap (𝓞 K₁) K₁)) (CommRingCat.ofHom (algebraMap K₁ ℂ)))
  obtain ⟨κ, hκ⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (algebraMap K₁ ℂ))) (FU.u i Pe) hyu.symm
  have hadd : ∀ (j : Fin D.p ⊕ Fin D.q) z w, e _ (z + w) ≫ Φ j = (e _ z ≫ Φ j) * (e _ w ≫ Φ j) := fun j z w => by
    have := (hΦl j).1
    rw [(he _).2.2.1, MonObj.mul_comp]
  have tie : ∀ (j : Fin D.p ⊕ Fin D.q) z, κ (κ'.symm (e _ z ≫ Φ j)) = FU.ex i Pe (F j z) := fun j z => by
    refine additive_ext (he j.isLeft).1.2.2.2.1 (u := fun z => κ (κ'.symm (e _ z ≫ Φ j)))
      (v := fun z => FU.ex i Pe (F j z)) (fun z w => ?_) (fun z w => ?_) (fun a s => ?_) z
    · simp only [hadd, map_mul]
    · simp only [map_add (f := _), FU.ex_add i Pe hP]
    · apply Over.OverMorphism.ext
      simp only [map_smul, hFP, hκ]
      refine htie j.isLeft ⟨Z.f j a, Z.pure j a⟩ s _ (Over.w _) ?_
      refine (hκ' _).symm.trans ?_
      rw [κ'.apply_symm_apply, Over.comp_left, hee, Category.assoc, Category.assoc, ← Over.comp_left, hΦt]
      rfl
  have hρ : σ (2 * ω true - 1) = H.rt0 := hσω true
  have hsq : (2 * ω true - 1) ^ 2 = -(H.d : 𝓞 K₁) := hσi (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hneg : 2 * ω false - 1 = -(2 * ω true - 1) := hσi (by rw [map_neg, hρ, hσω]; rfl)
  have tP := hasType_of_isTen hL.polBaseChange E H _ _ (C true) _ _ _ ⟨t true⟩
  have tM := hasType_of_isTen hL.polBaseChange E H _ _ (C false) _ _ _ ⟨t false⟩
  rw [Z.sigP.1, Z.sigP.2] at tP
  rw [Z.sigM.1, Z.sigM.2, hneg] at tM
  refine ⟨K₁, inst, hk, 2 * ω true - 1,
    { split := hsplit K₁ fun τ a => hkK ((le_sup_right : k₀ ≤ k ⊔ k₀) (hconj τ a))
      ρ_sq := hsq
      A := T
      B := B
      typeP := tP
      typeM := (hasType_neg_iff E H _ _ _ _ 0 1 hsq).2 tM
      typeB := hasType_of_moduli Xo K₁ hk (2 * ω true - 1) hρ B.t y t₀ m m' hy
      hh := Z.hh
      φ := Φ
      lin := hΦl
      onto := fun w => ?_
      weil := fun j => ?_ }, y, t₀, m, m', gA, tyA, PA, e, F, le_sup_left.trans hkK, hρ, rfl, hy, hyu,
    fun b => ⟨hty b, he b⟩, hFP, fun j z x hx hxe => ?_⟩
  · obtain ⟨v, hv⟩ := FU.ex_onto i Pe hP (κ (κ'.symm w))
    obtain ⟨n, hn, hs⟩ := Z.span
    obtain ⟨z, rfl⟩ := exists_sum F hP.2.2.2.1 hn (fun a => by
      obtain ⟨x, hx⟩ := hs a
      exact ⟨fun j => PA _ (x j), by simp only [hFP, ← map_sum, ← hx, map_nsmul]⟩) v
    refine ⟨fun j => e _ (z j), κ'.symm.injective (κ.injective ?_)⟩
    let ex : Multiplicative (Fin g → ℂ) →* (Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G) :=
      MonoidHom.mk' (fun s => FU.ex i Pe s.toAdd) fun a b => FU.ex_add i Pe hP _ _
    rw [← hv, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp only [Function.comp_def, tie]
    have := map_list_prod ex (List.ofFn fun r : Fin (D.p + D.q) =>
      Multiplicative.ofAdd (F (finSumFinEquiv.symm r) (z (finSumFinEquiv.symm r))))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum,
      Equiv.sum_comp finSumFinEquiv.symm fun j => F j (z j)] at this
    exact this
  · exact (PairingFibre.lamEq_weilEq_over_ring hL _ (T j.isLeft).pol (T j.isLeft).pol B.pol (T j.isLeft).pol
      (Φ j) (Φ j) ((T j.isLeft).t.act.act (Z.hh j)) (𝟙 _) (hΦl j).1 (hΦl j).1 ((T j.isLeft).t.act.hom _)
      inferInstance ℂ σ).1 (hΦp j)
  · have hx' : κ'.symm (e _ z ≫ Φ j) = Over.homMk x hx :=
      κ'.symm_apply_eq.2 (Over.OverMorphism.ext (hxe.symm.trans (hκ' (Over.homMk x hx)).symm))
    rw [← tie, hx', hκ]
    rfl

end GlobalTheory.CM.ExObj
end
