module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle161
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem rep_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z s - z' s ∈ b.S _) (hr : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, hc, hz⟩ := hr
  exact ⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ} (E : Frame (Φ := Φ) d)
  (σ : ∀ T : C, E.D ⟶ T) {t : Fin d → Φ.A.obj E.D} (ht : E.Coords t) {u : Fin d → ∀ T : C, Φ.A.obj T}
  (hu : ∀ i T, (Φ.A.map (σ T)).hom (t i) = u i T)

include ht hu

theorem a_eq (i : Fin d) {T T' : C} (φ : T ⟶ T') : E.a σ i φ = u i T' - (Φ.A.map φ).hom (u i T) := by
  have e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i)) := by
    rw [Functor.map_comp]; rfl
  rw [Frame.a, ht, hu, e, hu]

theorem form_eq {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I x s = wz u I s * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form wz
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [a_eq E σ ht hu]

theorem form_sub_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {r : ℕ} (I : Fin r → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C r) (l : Φ.A.obj (s.obj (Fin.last r)))
    (hl : (Φ.A.map (σ _)).hom x - l ∈ Φ.J.S _) :
    E.form σ I x s - wz u I s * l ∈ (Fil ((r : ℤ) + 1)).S _ := by
  have hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T' := fun i T T' φ => by
    rw [← a_eq E σ ht hu]
    exact E.mem _ _ _
  have h1 := wz_mem hF u hm I s
  have h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    simpa [hF.one] using hl
  have h3 := hF.mul r 1 _ h1 h2
  rw [form_eq E σ ht hu, ← mul_sub]
  simpa using h3

end Frame

theorem stLoc : StFrame → KH.LocGr → KH.PolyTf → StLoc := by
  intro hFr hLoc hPoly O _ l s hb X q W d c u hu r hr
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := hFr l s hb q c u hu
  obtain ⟨Q, hQ⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)
  obtain ⟨-, hL⟩ := hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj := fun T => by
    obtain ⟨-, V, hV, h⟩ := T.property
    rwa [Set.mem_singleton_iff.1 hV] at h
  have key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP (SS q l s W)) (fun i T => u i T.obj) I.1 z *
          (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot 1 one_ne_zero
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem isLift_lft {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) : IsLift (q := q) W t (fun i T => lft W T (t i)) :=
  fun i T h => lft_spec T h (t i)

theorem rep_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    (c : CH.H (sq a b) j) (h : Rep a b (fun s => 0) c) : c = 0 := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  have e : f = 0 := by
    funext s
    apply Subtype.ext
    rw [show (show sqM a b _ from f s).1 = _ from hz s]
    simp
  subst e
  rfl

theorem van : StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → StVan := by
  intro hFr hL hP O _ l s hb X q W d c r j hrs hjr
  obtain ⟨E, σ, θ, hGr, hbot, -, -, -⟩ := hFr l s hb q c _ (isLift_lft W c.t)
  obtain ⟨Q, hQ⟩ := hP (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hCr : ∀ r' ≤ (r : ℤ) + 1, Q.Crit (sFil (SS q l s W)) r' := fun r' h => (hQ r' (by omega)).1
  have key := hL Q (GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)) E σ hGr (r : ℤ) hCr j
  rcases lt_or_gt_of_ne hjr with hlt | hlt
  · obtain ⟨h1, -⟩ := key.2 (r - j) (by omega)
    have all : ∀ cl : CH.H (gr (sFil (SS q l s W)) (r : ℤ)) j, cl = 0 := by
      intro cl
      obtain ⟨x, hx, hR⟩ := h1 cl
      have x0 : ∀ I, x I = 0 := fun I => by
        have h := hx I
        rw [hbot (r - j) (by omega)] at h
        exact h
      have e : (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) = fun s => 0 := by
        funext s
        refine Finset.sum_eq_zero fun I _ => ?_
        simp [x0, Frame.form]
      rw [e] at hR
      exact rep_zero _ _ cl hR
    exact ⟨fun a b => (all a).trans (all b).symm⟩
  · exact key.1 (by exact_mod_cast hlt)

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FilTop

section Inj
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_pullC_bij (a b : IdF A) (ha : ∀ T, a.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (n : ℕ) :
    Function.Bijective ((toSq a b ha).pullC n) := by
  have hτ : ∀ T, Function.Bijective ((toSq a b ha).τ T) := by
    intro T
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (Ideal.Quotient.mk (b.S T) (show A.obj T from x)) = Ideal.Quotient.mk (b.S T) (show A.obj T from y) :=
        congrArg Subtype.val hxy
      rw [Ideal.Quotient.eq, hb T, Ideal.mem_bot, sub_eq_zero] at h1
      exact h1
    · obtain ⟨z, hz⟩ := z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨x, rfl⟩
  refine ⟨fun f g hfg => ?_, fun f' => ?_⟩
  · funext s
    exact (hτ _).1 (congrFun hfg s)
  · refine ⟨fun s => Function.surjInv (hτ _).2 (f' s), ?_⟩
    funext s
    exact Function.surjInv_eq (hτ _).2 (f' s)

end Inj

theorem pull_inj_of_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
    (hb : ∀ n, Function.Bijective (m.pullC n)) (n : ℕ) : Function.Injective (m.pull n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  change m.pull n (Submodule.Quotient.mk z) = 0 at hx
  unfold CH.Mor.pull Cx.Hom.mapH at hx
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  change m.pullC n z.1 ∈ (CH.cx F').B n at hx
  change z.1 ∈ (CH.cx F).B n
  cases n with
  | zero =>
    have h0 : m.pullC 0 z.1 = 0 := hx
    have : z.1 = 0 := (hb 0).1 (h0.trans (map_zero _).symm)
    rw [this]; exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g0, rfl⟩ := (hb n).2 g
    refine ⟨g0, (hb (n + 1)).1 ?_⟩
    change m.pullC (n + 1) (CH.d F n g0) = m.pullC (n + 1) z.1
    rw [← CH.Mor.d_pullC]
    exact hg

theorem fil_top_vanish : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  intro _ _ _ _ _ hKIso _ K _ _ X q _ d _ j x hx
  obtain ⟨U, hU⟩ := (GlobalTheory.T.exists_smooth_coordinate_cover q).2 d inferInstance
  have h𝒱 : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hk := hKIso q U (d + 1) (fun α => by rw [hU α]; omega) (Set.range U.U) h𝒱 j
  have h0 : quoK q (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ) j x = 0 := (hk.2 (d + 1) le_rfl x).1 hx
  have hb : ∀ T, (sFil (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ)).S T = ⊥ := by
    intro T
    change T.obj.pdPow ((d + 1 : ℕ) : ℤ).toNat = ⊥
    rw [Int.toNat_natCast]
    exact T.property.1.1
  have hinj := GlobalTheory.CompanionTheory.FilTop.pull_inj_of_bij _
    (GlobalTheory.CompanionTheory.FilTop.toSq_pullC_bij (sFil (KS q (d + 1) (Set.range U.U)) 0) _ (fun T => T.obj.pdPow_zero) hb) j
  have h1 : resK q (KS q (d + 1) (Set.range U.U)) j x = 0 := hinj (by
    rw [map_zero]; exact h0)
  exact hk.1.1 (h1.trans (map_zero _).symm)

end GlobalTheory.CompanionTheory.FilTop
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.ChartAlg in

theorem _root_.GlobalTheory.T.exists_chart_from_coordinates : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
  intro O R _ _ _ I γ l s hb X q κ hκ V d c
  let a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  have hstr : algebraMap O Γ(X, V) = strV q V := rfl
  have hE : (MvPolynomial.eval₂Hom (algebraMap O Γ(X, V)) c.t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale := c.etale
  have hF : Module.Flat O Γ(X, V) := flat_of_etale c.t hE
  let iL : R →+* R ⊗[O] Γ(X, V) := Algebra.TensorProduct.includeLeftRingHom
  have hl : ∀ x : R ⊗[O] Γ(X, V), (l : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun x h => by
    have := tf_tensor (G := Γ(X, V)) (O := O) (pdP γ s) l (hb.tf s) x (by rw [h]; exact zero_mem _)
    rw [hb.nil, Ideal.map_bot] at this
    exact this
  have hlk : ∀ (k : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => intro x h; simpa using h
    | succ k ih =>
      intro x h
      refine ih x (hl _ ?_)
      rw [← h, pow_succ']
      ring
  have hn : ∀ n : ℕ, n ≠ 0 → ∀ x : R ⊗[O] Γ(X, V), (n : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun n hn0 x h => by
    obtain ⟨k, u, hu⟩ := hb.dv n hn0
    refine hlk k x ?_
    have e := congrArg iL hu
    rw [map_mul, map_pow, map_natCast, map_natCast] at e
    rw [← e, mul_comm (n : R ⊗[O] Γ(X, V)), mul_assoc, h, mul_zero]
  obtain ⟨δ, hδ⟩ := exists_dp γ iL hn
  have hP := dividedPowerFiltration_eq_map γ iL δ hδ
  let g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL :=
    (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[O] R ⊗[O] Γ(X, V)).toRingHom
  let ψ : R ⧸ I →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  have hcomp : g.comp (strV q V) = ψ.comp κ := RingHom.ext fun a => by
    change Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] (algebraMap O Γ(X, V) a)) = ψ (κ a)
    rw [hκ]
    change _ = Ideal.Quotient.mk _ ((algebraMap O R a) ⊗ₜ[O] (1 : Γ(X, V)))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸ I.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp q c.affine, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]⟩
  have hnil : IsNilpotent (I.map iL) := ⟨s, by
    have h := pow_le_pdP δ s
    rw [hP, hb.nil, Ideal.map_bot] at h
    exact le_bot_iff.1 h⟩
  let D : Thick (nlFun γ 0 X q κ) := mkT (R ⊗[O] Γ(X, V)) iL (I.map iL) δ ⟨fun h => (h rfl).elim, fun _ => hnil⟩ hδ y
    (fun r => rfl)
  have hin : InU V D := top_le_specMap c.affine g
  let c' : Chart γ 0 q κ V d :=
    { D := D
      t := fun k => (1 : R) ⊗ₜ[O] c.t k
      etale := etale_tensor c.t hE
      J_eq := rfl
      inV := hin
      rep := fun B' y' hy' => rep_tensor hstr hκ c.affine y (fun r => rfl) g (fun f => rfl) rfl B' y' hy' }
  have key : ∀ (r : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) * x ∈ pdP δ r → x ∈ pdP δ r := fun r x hx => by
    rw [hP] at hx ⊢
    exact tf_tensor (pdP γ r) l (hb.tf r) x hx
  refine ⟨c', RingEquiv.refl _, ⟨?_, fun r x hx => ?_⟩, fun r => rfl, fun k => rfl, fun f => ?_⟩
  · change pdP δ s = ⊥
    rw [hP, hb.nil, Ideal.map_bot]
  · exact key r x hx
  · have := evalAt_specMap c.affine g (pt D) rfl hin
    exact RingHom.congr_fun this f
end

section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatNil

theorem isDPMorphism_ι {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) := by
  refine ⟨Ideal.map_comap_le, ?_⟩
  intro n a ha
  exact (Lat.ι_γ f ξ l M hc ha).symm

theorem dividedPowerFiltration_eq_bot : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), pdP (Lat.γ f ξ l M hc) m = ⊥ := by
  intro W B _ _ _ f ξ l M m h hc
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have h1 : Lat.ι f ξ l M x ∈ pdP (Lat.γB f ξ) m := dividedPowerFiltration_map (isDPMorphism_ι f ξ l M hc) m hx
  rw [GlobalTheory.T.divided_power_filtration_span_pow f ξ m, h.nil, Ideal.mem_span_singleton, zero_dvd_iff] at h1
  exact Lat.ι_injective f ξ l M (by rw [h1, map_zero])

end GlobalTheory.CompanionTheory.LatNil
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.chart_divided_powers_graded_constant : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.ChartFil.chart_grConst | exact GlobalTheory.CompanionTheory.ChartFil.chart_grConst | (intros; apply GlobalTheory.CompanionTheory.ChartFil.chart_grConst <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.stable_family_properties : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  first | exact @GlobalTheory.CompanionTheory.StFam.st_all | exact GlobalTheory.CompanionTheory.StFam.st_all | (intros; apply GlobalTheory.CompanionTheory.StFam.st_all <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrSplitField

theorem exists_step {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B}
    (γ : DividedPowers I) (i : ℕ) :
    ∃ C : Submodule K B, (∀ n ∈ C, n ∈ pdP γ i) ∧ (∀ n ∈ C, n ∈ pdP γ (i + 1) → n = 0) ∧
      ∀ x ∈ pdP γ i, ∃ n ∈ C, x - n ∈ pdP γ (i + 1) := by
  have hQ : (pdP γ (i + 1)).restrictScalars K ≤ (pdP γ i).restrictScalars K :=
    fun x hx => (Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, (Nat.le_succ i).trans hr, hz⟩ :
      pdP γ (i + 1) ≤ pdP γ i) hx
  obtain ⟨c, hc⟩ := exists_isCompl
    (⟨(pdP γ (i + 1)).restrictScalars K, hQ⟩ : Set.Iic ((pdP γ i).restrictScalars K))
  have hinf : (pdP γ (i + 1)).restrictScalars K ⊓ c.1 = ⊥ := congrArg Subtype.val hc.inf_eq_bot
  have hsup : (pdP γ (i + 1)).restrictScalars K ⊔ c.1 = (pdP γ i).restrictScalars K :=
    congrArg Subtype.val hc.sup_eq_top
  refine ⟨c.1, fun n hn => c.2 hn, fun n hn hn' => ?_, fun x hx => ?_⟩
  · have : n ∈ (pdP γ (i + 1)).restrictScalars K ⊓ c.1 := ⟨hn', hn⟩
    rw [hinf] at this
    simpa using this
  · have hx' : x ∈ (pdP γ (i + 1)).restrictScalars K ⊔ c.1 := by
      rw [hsup]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    exact ⟨z, hz, by simpa using hy⟩

theorem nonempty_grSplit : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  intro K B _ _ _ I γ m hm
  choose C hC₁ hC₂ hC₃ using fun i : ℕ => exists_step (K := K) γ i
  exact ⟨{
    N := fun i => C i
    ν := fun i => (C i).subtype
    mem := fun i n => hC₁ i n n.2
    inj := fun i n h => Subtype.ext (hC₂ i n n.2 h)
    surj := fun i x hx => by
      obtain ⟨n, hn, h⟩ := hC₃ i x hx
      exact ⟨⟨n, hn⟩, h⟩
    nil := hm }⟩

end GlobalTheory.CompanionTheory.GrSplitField
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedTower

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem pull_sqLe_pull_toSq {a b a' b' : IdF A} (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤)
    (hle : ∀ T, a.S T ≤ a'.S T) (hb : ∀ T, b.S T ≤ b'.S T) (j : ℕ) (z : CH.H (CH.modF A) j) :
    (sqLe hle hb).pull j ((toSq a b ha).pull j z) = (toSq a' b' ha').pull j z := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Sq

theorem trM_redM {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) (n j : ℕ) (z : HO Q j) :
    trM Q r c n j (redM Q r (c ^ (n + 1)) j z) = redM Q r (c ^ n) j z :=
  pull_sqLe_pull_toSq (fun _ => rfl) (fun _ => rfl) (fun _ => le_rfl) (stdI_le Q r c n) j z

end GlobalTheory.CompanionTheory.RedTower
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | exact GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | (intros; apply GlobalTheory.CompanionTheory.BZMir.continuous_gpProj <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

theorem _root_.GlobalTheory.T.isClosed_mirabolicParabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | exact GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | (intros; apply GlobalTheory.CompanionTheory.MirGP.isClosed_HGP <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

theorem _root_.GlobalTheory.T.mirabolic_phi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPhiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPhiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPhiMinus <;> assumption)
end
