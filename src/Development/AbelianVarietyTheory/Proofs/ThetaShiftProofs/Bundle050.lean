module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle041
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle040
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle038
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibres
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.ExFr

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem one_eq : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  have := m.cm.e_comm
  rw [m.base] at this
  exact this

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_eq m).symm
    · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw, a, ← spMap_comp]
      have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h).trans (one_eq m)

theorem scale_over (s : S) : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) =
    spMap (algebraMap S (DualNumber S)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, scale_over]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem exists_lift {T : Over (Sp S)} (v : T.left ⟶ Xo.univ.t.G.left) (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) :
    ∃ w : T ⟶ t'.G, w.left ≫ m.φ = v :=
  ⟨Over.homMk (m.cart.1.lift v T.hom hv) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem push_prod {n : ℕ} (u : Fin n → (epsR S ⟶ t'.G)) :
    ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (epsR S) (u i)).prod).left := by
  have := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    choose u' hu' using fun i => exists_lift m (T := epsR S) (u i).left (Over.w (u i))
    have e : u = fun i => pushHom m.cart (epsR S) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
    · apply m.cart.1.hom_ext
      · rw [Category.assoc]; exact (hu' i).trans (hu i)
      · have hv : (v i).left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w (v i)
        rw [Over.w, Category.assoc, hv, scale_over]; rfl
    · apply m.cart.1.hom_ext
      · rw [e] at hw
        exact hw.symm.trans (push_prod m u').symm
      · rw [Over.w, Over.w]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (epsR S) (u i), fun i => ?_, (push_prod m u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu, Category.assoc]; rfl

end GlobalTheory.ArcQ.ExFr


open GlobalTheory.ArcQ.ExFr in
theorem GlobalTheory.ArcQ.exists_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → (IsField A ∨ PushInvertible Y.t.G Y.t.PP.L) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (z : Sp S ⟶ Xo.XF c), (ι.comp (PowerSeries.C (R := A))).Flat → z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ ≫ Xo.s = sOf c S → (∀ τ x, algebraMap c.F S (embK c τ x) = ι (PowerSeries.C (R := A) (ρ τ x))) → ∃ y : FrPt Xo c S, y.x = z ≫ pullback.fst _ _ ∧ IsArcFr W e th ι y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e th hB hth hA S _ _ ι z hfl hz hs hρ
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m1, hm1⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap ι ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap ι), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ hz n
  open Matrix GlobalTheory.BasisUniv in
  have arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
    intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
    obtain ⟨v₀, hv₀, hB⟩ := hB
    obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
    have hsm : Smooth W.t.G.hom := W.t.semi.smooth
    have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
    have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
    obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
    obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart
  
    have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
      have ht : GtTanR (e τ k) :=
        ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
      obtain ⟨U, hU, -⟩ := hcomb _ ht
      exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
    choose U hU using hU
    choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
    choose v' hv' using fun j => exists_lift ι m2.cart (v j)
    have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
    have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
      Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
    have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
      Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
        rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
    have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
    have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
      have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
      funext j
      have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
      simpa [Matrix.vecMul, dotProduct] using this
    refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
      fun w hw hwe => ?_⟩⟩
    · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
      funext j
      have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
      simpa [Matrix.vecMul, dotProduct] using this
    · obtain ⟨z, hz, -⟩ := hb'.2 w hw
      simp only [comb_iff hy' hb' (hU' τ) hz]
      refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
        (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
      have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
      have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
      simpa only [comb_iff hy hv (hU τ) hc] using this
  obtain ⟨u, hu1, hu2⟩ := arcBasis_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB S ι hfl t' m2
  obtain ⟨⟨θ, hθ, -⟩, -⟩ := GlobalTheory.existsUnique_thetaOf hL hL2 E H Dw l Xo c O β Y A b a χ W th hth
  have hnz := fun g => (GlobalTheory.ThetaAllFibres.theta_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ hA g).2
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2).1 g2) W.t.PP.isLB t'.PP.isLB θ
  have hI2 : IsoMaps w2 σ' (thfPull W.t.PP.L m2.φ θ) := fun (i : PUnit → W.t.PP.L.ι) k => fn_ext fun y hy =>
    (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      ((hσ' _ (𝟙 _) y (i PUnit.unit) k (mem_pull.1 hy.1) hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))
  have nz := GlobalTheory.SectionBaseChange.fibre_nonzero_of_pull t'.PP.isLB hσ' m2.cart.1 hnz
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have hLB : LBIso t'.PP.L (Xo.univ.t.PP.L.pull m1.cm.F) := by
    obtain ⟨w, hw, -⟩ := m1.lin
    exact ⟨w, hw⟩
  have hgen := GlobalTheory.SectionBaseChange.generates hL.secBaseChange (GlobalTheory.Obj.toPolAV Xo.univ) m1.cart.1 t'.PP.isLB hLB σ' nz
  obtain ⟨s, w1, s1, r1, hI1, hg, hsgen⟩ := frame_of_gen Xo _ t' m1 σ' hgen
  have eig : ∀ (τ : E →+* ℂ) (w : epsR S ⟶ t'.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← hρ]; exact eig_iff m1 w x _
  refine ⟨⟨z ≫ pullback.fst _ _, (Category.assoc _ _ _).trans hs, fun τ k => (u τ k).left ≫ m1.φ,
    fun τ k => (tan_iff m1 _).2 ((hu2 τ).1 k).1, fun τ k => (eig τ _).2 ((hu2 τ).1 k).2, fun τ w hw hw' => ?_,
    s, hsgen⟩, rfl, z, t', m1, m2, m.φ, hz, rfl, m.cart.1.w, hm1.symm, hn.symm.trans hm2, fun τ k => ?_,
    θ, w1, w2, σ', s1, _, hθ, r1, ⟨g2, r2⟩, hI1, hI2, fun _ _ => rfl, hg⟩
  · obtain ⟨w', rfl⟩ := exists_lift m1 (T := epsR S) w hw.1
    exact (existsUnique_congr fun cf => comb_iff m1 (u τ) cf w').2
      ((hu2 τ).2 w' ((tan_iff m1 w').1 hw) ((eig τ w').1 hw'))
  · obtain ⟨v, hv, hv'⟩ := hu1 τ k
    exact ⟨v, (u τ k).left, hv, rfl, hv', Over.w (u τ k)⟩
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isHolTo_comp_univ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  unfold IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ (Set.univ : Set V) ∧ ⊤ ≤ (fun z => y (φ z)) b ⁻¹ᵁ U} =
      φ ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and, hB b]
  rw [hset]
  exact ⟨ho.preimage hφ.continuous, hd.comp hφ.differentiableOn (fun b hb => hb)⟩

theorem isHolTo_exp_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ (fun z => (Fu.ex i P z).left) := by

  have hper : IsHolPeriods (Fu.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have hjoint : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (Fu.ex i P bz.2).left) :=
    (Fu.21 i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  have hφ : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hmem : ∀ z : Fin g → ℂ, ((0 : Fin 0 → ℂ), z) ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
    fun z => Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)
  have hcomp := isHolTo_comp_univ hjoint hφ hmem
  exact hcomp

theorem point_exp_eq_of_isometry : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → (∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v) → (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e) → (∀ u, P' (gm u) = L (P u)) → Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  intro hK E _ _ _ H D l Xo σ g ty Fu i i' P P' gm L hpq hρ hty hA hP hP' hiso hmark hPL

  have hpt : Fu.u i P = Fu.u i' P' := by
    refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hρ hty
      (Fu.Di i) (Fu.Di i') (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.22 i P hP).1, (Fu.22 i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.22 i' P' hP').1, (Fu.22 i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP', Fu.ex_weil i' P' hP',
        Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ?_

    exact ⟨gm, L, hiso, hmark, fun a => ⟨gm (Fu.t i a) - Fu.t i' a, by rw [hA, one_smul]; abel⟩, hPL⟩

  have hii : i = i' := Fu.disj i i' P P' hP hP' hpt
  subst hii

  letI := H.starRing
  have hex := GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hmark
    (fun v => ⟨gm (Fu.t i v) - Fu.t i v, by rw [hA, one_smul]; abel⟩) hPL
  exact ⟨hpt, hex.2⟩

end GlobalTheory.ArcCM
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstSpan

open GlobalTheory.FieldBaseChange

theorem exists_relation {R M J : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Fintype J]
    (σ σ' : J → M) (h : ∀ s, ∃ t : R, t ≠ 0 ∧ t • s ∈ Submodule.span R (Set.range σ)) (s : M) :
    ∃ (t : R) (r : J → R), (t = 0 → ∃ i, r i ≠ 0) ∧ t • s + ∑ i, r i • σ' i = 0 := by
  classical
  choose t ht hm using h
  let v : Option J → M := fun o => o.elim s σ'
  have hn : ¬ LinearIndependent R (fun o => t (v o) • v o) := fun hi => by
    have := linearIndependent_le_span_aux' _ hi (Set.range σ) (by rintro _ ⟨o, rfl⟩; exact hm _)
    have h2 := Fintype.card_range_le σ
    rw [Fintype.card_option] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hn
  refine ⟨g none * t s, fun i => g (some i) * t (σ' i), fun h0 => ?_, ?_⟩
  · cases o with
    | none => exact absurd h0 (mul_ne_zero ho (ht _))
    | some i => exact ⟨i, mul_ne_zero ho (ht _)⟩
  · simpa only [Fintype.sum_option, smul_smul, v, Option.elim] using hg

theorem map_relation {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype J] {t : R} {s : M} {r : J → R}
    {σ : J → M} (h : t • s + ∑ i, r i • σ i = 0) (ev : M →ₗ[R] R) : t * ev s + ∑ i, r i * ev (σ i) = 0 := by

  simpa only [map_add (f := _), map_sum, map_smul, map_zero, smul_eq_mul] using congrArg ev h

theorem smul_eq_zero_of_relation {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype J] {t : R} {s : M}
    {r : J → R} {σ : J → M} (h : t • s + ∑ i, r i • σ i = 0) (hr : ∀ i, r i = 0) : t • s = 0 := by
  simpa only [hr, zero_smul, Finset.sum_const_zero, add_zero] using h

theorem eq_zero_of_smul {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Smooth G.hom]
    (L : LB G.left) (j : ℤ) {t : R} (ht : t ≠ 0)
    (s : SecOver G.hom (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => j))) (h : t • s = 0) : s = 0 := by
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have : IsDominant (Out.jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (Out.jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (Out.jK R)).flip
  have hp : pullback.fst G.hom (Out.jK R) ≫ G.hom =
      pullback.snd G.hom (Out.jK R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (Out.jK R)) k =
      pullback.fst G.hom (Out.jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  have hρ := ConstFam.pullOver_injective_of_dominant L (fun _ : Fin 1 => j) hp hφ
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := fun h => ht (hinj (h.trans (map_zero _).symm))
  have e := congrArg (pullOver L (fun _ : Fin 1 => j) hp hφ) h
  rw [map_smulₛₗ, map_zero] at e
  exact hρ (((smul_eq_zero.1 e).resolve_left ht').trans (map_zero _).symm)

def valLin {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (x : Sp R ⟶ Y) (hx : x ≫ π = 𝟙 _) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : FnOver π U →ₗ[R] R where
  toFun f := valR x U f
  map_add' f g := Points.valR_add x U h f g
  map_smul' c f := (Points.valR_mul x U h (constFn π U c) f).trans
    (congrArg (· * _) (Points.valR_constFn_of_section π x hx U h c))

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : _root_.GlobalTheory.ArcPts.GtAn a}

theorem tau_ne_zero (Ξ : ConstPts W Λ) (v : Λ.A.V) (j : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U j) :
    Ξ.τ v j ≠ 0 := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  have hj : ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U
      (fun _ => FrameValue.chartAt a.D₀.P.isLB (Λ.u.ex v.2).left, jM) := (top_le_iff_cpt _ _).2 ⟨mem_pull.2
    ((congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)), hM⟩
  refine (isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v j jM _ h hj)).mpr ?_)).ne_zero
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne _ v.2 h₀)).map _)

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (σ : Out.H0 W.P.U.LG.L j), ∃ f, IsComb Λ.A j Set.univ f ∧ Ξ.Vals σ f ∧ ((∀ v, f v = 0) → ∀ i, σ.f i = 0) := by
  classical
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ s
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨-, rep, hrep⟩ := exists_representatives_mod_nsmul Λ.A.X j hj
  obtain ⟨hfn, hfin, -⟩ := ArcThetaSpaces.sections_theta hL hL2 E H D l c O β b a Λ
  let fn := fun x => TwistedTheta.secFn a.D₀ Λ.u j (Λ.ε (rep x)) (Λ.A.ct (rep x))
  have hinj : ∀ x, Function.Injective (fn x) := fun x => TwistedTheta.secFn_injective (Λ.ct _)
  have hmem : ∀ x s, fn x s ∈ Λ.A.Theta j (rep x) := fun x s => (hfn j (rep x) hj).1 s
  have : ∀ x, Module.Finite ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x))) := fun x =>
    have := hfin.1 j (rep x) hj
    Module.Finite.of_injective ((fn x).codRestrict _ (hmem x)) fun _ _ e => hinj x (congrArg Subtype.val e)
  let bas := fun x => Module.finBasis ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))
  let th := fun x i => fn x (bas x i)
  have hth : ∀ x, LinearIndependent ℂ (th x) := fun x =>
    (bas x).linearIndependent.map' (fn x) (LinearMap.ker_eq_bot.2 (hinj x))
  have hrep' : ∀ α, ∃! x, ∃ mu, Λ.ε (rep x) + j • mu = α := fun α => by
    refine (existsUnique_congr fun x => ⟨?_, ?_⟩).1 (hrep (Λ.ε.symm α))
    · rintro ⟨m, hm⟩
      exact ⟨Λ.ε m, by rw [← map_nsmul, ← map_add (f := _), ← hm, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Λ.ε.symm m, by rw [map_add (f := _), map_nsmul, LinearEquiv.symm_apply_apply]⟩
  have hrep'' : ∀ x x' mu, rep x = rep x' + j • mu → x = x' := fun x x' mu h =>
    (hrep (rep x)).unique ⟨0, by simp⟩ ⟨mu, h⟩
  choose m₀ hm₀ using fun i : Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))) =>
    ConstFam.exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε (rep i.1)) (bas i.1 i.2)
  choose f σ hf hE using fun i => hm₀ i _ le_rfl
  have hspan := ConstFam.exists_pow_smul_mem_span hW hL.globalFns hj W.P.U _ hrep' bas m₀ f σ hf hE
  choose m σ' hσ' using fun i : Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))) =>
    GlobalTheory.T.exists_section_values_formalThetaSum hL hL2 E H D l Xo c O β Y b a χ W Λ Ξ j (rep i.1) (th i.1 i.2) (hmem _ _)
  obtain ⟨t, r, hne, hrel⟩ := exists_relation (R := ℂ⟦X⟧) (M := SecOver W.t.G.hom
    (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ)))) σ σ'
    (fun s => (hspan s).elim fun n hn => ⟨_, pow_ne_zero n PowerSeries.X_ne_zero, hn⟩) s
  have hφ : Function.Injective (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) := IsFractionRing.injective _ _
  set φ := algebraMap ℂ⟦X⟧ ℂ⸨X⸩ with hφdef
  let S : Λ.A.V → ℂ⸨X⸩ := fun v => ∑ i, (φ (r i) * HahnSeries.single (m i : ℤ) (1 : ℂ)) *
    Λ.A.FSum j (rep i.1) (th i.1 i.2) v
  have key : ∀ v jL, ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U jL →
      φ t * φ (FormalValue.secVal W.P.U.toUnifPre s (Ξ.x v).left jL) + S v * φ (Ξ.τ v jL) ^ j = 0 := by
    intro v jL h
    have hx : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) ≫ W.t.G.hom = 𝟙 _ := (Over.w (Ξ.x v)).trans (Spec.map_id _)
    let ev := (valLin W.t.G.hom (Ξ.x v).left hx _ (FormalValue.top_le_secChart (U := W.P.U.toUnifPre) h)).comp
      (chartLin W.t.G.hom (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ)))
        (fun _ => jL))
    have e₀ : t * FormalValue.secVal W.P.U.toUnifPre s (Ξ.x v).left jL +
        ∑ i, r i * FormalValue.secVal W.P.U.toUnifPre (σ' i) (Ξ.x v).left jL = 0 := map_relation hrel ev
    have e := congrArg φ e₀

    simp only [map_add (f := _), map_sum, map_zero, map_mul] at e
    refine Eq.trans (congrArg₂ (· + ·) rfl ?_) e
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hσ' i v jL h]
    ring
  have hS : (∀ v, S v = 0) → ∀ i, r i = 0 := fun h i => by
    have := Λ.A.eq_zero_of_sum_FSum hrep'' hth
      (r := fun x k => φ (r ⟨x, k⟩) * HahnSeries.single (m ⟨x, k⟩ : ℤ) (1 : ℂ))
      (fun v => (Fintype.sum_sigma _).symm.trans (h v)) i.1 i.2
    exact hφ (((mul_eq_zero.1 this).resolve_right (HahnSeries.single_ne_zero one_ne_zero)).trans (map_zero _).symm)
  have ht : t ≠ 0 := fun h0 => by
    obtain ⟨i, hi⟩ := hne h0
    refine hi (hS (fun v => ?_) i)
    obtain ⟨jL, hjL⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) (cpt ℂ⟦X⟧))
    have h := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x v).left) _).2 hjL
    have e := key v jL h
    rw [h0, map_zero, zero_mul, zero_add] at e
    exact (mul_eq_zero.1 e).resolve_right (pow_ne_zero _ fun e => tau_ne_zero Ξ v jL h (hφ (e.trans (map_zero _).symm)))
  have ht' : φ t ≠ 0 := fun h => ht (hφ (h.trans (map_zero _).symm))
  refine ⟨fun v => -(φ t)⁻¹ * S v, ?_, fun v jL h => ?_, fun h i => ?_⟩
  · let e := (Fintype.equivFin (Σ x, Fin (Module.finrank ℂ (ConstFam.SecBMod a.D₀ j (Λ.ε (rep x)))))).symm
    refine ⟨_, fun k => -(φ t)⁻¹ * (φ (r (e k)) * HahnSeries.single (m (e k) : ℤ) (1 : ℂ)), fun k => rep (e k).1,
      fun k => th (e k).1 (e k).2, fun k => ⟨trivial, hmem _ _⟩, fun v => ?_⟩
    refine (Finset.mul_sum _ _ _).trans ((e.sum_comp _).symm.trans (Finset.sum_congr rfl fun k _ => ?_))
    exact (_root_.mul_assoc _ _ _).symm
  · refine mul_left_cancel₀ ht' ((eq_neg_of_add_eq_zero_left (key v jL h)).trans ?_)
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_neg, mul_inv_cancel₀ ht', neg_one_mul, neg_mul]
  · have hr := hS fun v => (mul_eq_zero.1 (h v)).resolve_left (neg_ne_zero.2 (inv_ne_zero ht'))
    have := W.P.U.smooth
    exact congrArg (fun q => LB.Sec.f q i) (eq_zero_of_smul W.t.G _ _ ht s (smul_eq_zero_of_relation hrel hr))

end GlobalTheory.ConstSpan
end
end
