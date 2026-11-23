module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle716
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.exists_product_degenerationData_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I), ∃ (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ := by
  first | exact @GlobalTheory.SumDeg.exists_sum | exact GlobalTheory.SumDeg.exists_sum | (intros; apply GlobalTheory.SumDeg.exists_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.KerPol
open GlobalTheory.UPel.HT.Hecke

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h hh
  have hfib := GlobalTheory.T.hecke_bundle_trivial_geometric_fibre p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh
  obtain ⟨x, rfl⟩ := hh
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  have etaPow : ∀ (n : ℕ) (z : D.La), (o.eta z) ^ n = o.eta (n • z) := by
    intro n z
    induction n with
    | zero => rw [pow_zero, zero_smul, eta_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]
  set th : o.A ⟶ o.A := toUnit o.A ≫ o.eta (N • g x) with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, etaPow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.Hecke.KerPol
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem forget_map_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  intro p _ D R _ _ b N N' hd hc h3 M M' π hπ ⟨om⟩
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, ηu, hYf, hYe, HY⟩ := GlobalTheory.T.exists_finite_etale_level_lift_scheme p D R b N N' hc hd M.X M.s M.univ
  let T0 : Over M.X := Over.mk π
  have hw : ∀ a, ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = T0.hom := fun a => by
    have w : (om.φ : M'.univ.A.left ⟶ M.univ.A.left) ≫ M.univ.A.hom = M'.univ.A.hom ≫ π := om.cart.1.w
    have w2 : (M'.univ.eta a).left ≫ M'.univ.A.hom = 𝟙 M'.X := Over.w (M'.univ.eta a)
    show ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = π
    erw [Category.assoc, w, ← Category.assoc, w2, Category.id_comp]
  let lv0 : D.La → (T0 ⟶ M.univ.A) := fun a => Over.homMk ((M'.univ.eta a).left ≫ om.φ) (hw a)
  have hl0 : IsLift M.univ N' T0 lv0 :=
    GlobalTheory.T.harrisTaylor_isLevelLift_of_point p D R b N N' hd hc M.X M'.X M.s M'.s M.univ M'.univ π om T0 (𝟙 M'.X) lv0
      (Category.id_comp π) fun a => (Category.id_comp _).symm
  obtain ⟨g0, hg0, -⟩ := (HY T0 lv0).1 hl0
  have hlY : IsLift M.univ N' Y ηu := (HY Y ηu).2 ⟨𝟙 Y, fun a => Category.id_comp _⟩
  obtain ⟨h, hh, hha⟩ := GlobalTheory.T.exists_unique_point_of_level_lift_harrisTaylor p D R b N N' h3 hd hc M M' π hπ om Y ηu hlY
  have e1 : g0.left ≫ h = 𝟙 M'.X := by
    refine GlobalTheory.T.harrisTaylor_higherLevel_points_eq_of_same_image p D R b N N' hd hc M.X M.s M.univ M' π hπ om M'.X _ _ ?_ fun a => ?_
    · rw [Category.assoc, hh, Over.w g0, Category.id_comp]
      rfl
    · rw [Category.id_comp, Category.assoc, ← hha a, ← Over.comp_left, hg0 a]
      rfl
  let hY : Y ⟶ T0 := Over.homMk h hh
  have e2 : hY ≫ g0 = 𝟙 Y := by
    obtain ⟨f, -, hf⟩ := (HY Y ηu).1 hlY
    have a1 := hf (hY ≫ g0) fun a => by
      rw [Category.assoc, hg0 a]
      ext
      simp only [Over.comp_left, Over.homMk_left, hY, lv0]
      rw [hha a]
    have a2 := hf (𝟙 Y) fun a => Category.id_comp _
    rw [a1, a2]
  have e2' : h ≫ g0.left = 𝟙 Y.left := by
    have := congrArg (fun q => q.left) e2
    simpa [hY] using this
  haveI : IsIso g0.left := ⟨⟨h, e1, e2'⟩⟩
  have e : π = g0.left ≫ Y.hom := (Over.w g0).symm
  have hfe : IsFinite π ∧ Etale π := by
    rw [e]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨hfe.1, hfe.2, ⟨fun z => ?_⟩⟩

  obtain ⟨k, _, _, g, hg⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X z
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, g ≫ M.s = spMap β :=
    ⟨(Spec.preimage (g ≫ M.s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := M.univ.geom k g β hβ
  have hN' : 0 < N' := levelPos_of_coprime hc
  have hN : 0 < N := by omega
  have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
  let T : Over M.X := Over.mk g
  let lv : D.La → (T ⟶ M.univ.A) := fun a => I.ev N' a
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => I.add N' x y
  have hker : ∀ x, lv (N' • x) = 1 := fun x => (I.ker N' hN' hc _).2 ⟨x, rfl⟩
  have hlin : ∀ (c : D.O) x, lv (c • x) = lv x ≫ M.univ.act.act c := fun c x => I.lin N' c x
  haveI : IsLocallyNoetherian T.left := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k))
    infer_instance
  have hlv : IsLift M.univ N' T lv := by
    refine ⟨hadd, hker, hlin, fun x => ?_, fun k' _ _ x' => ?_⟩
    · show I.ev N' ((N' / N) • x) = toUnit T ≫ M.univ.eta x
      rw [hI x, I.ev_nsmul]
      have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) x
      rwa [Nat.mul_div_cancel' hd] at this
    · have h0 : TateAt M.univ N' g (fun a => lv a) := ⟨I, fun y => rfl⟩
      have h1 : TateAt M.univ N' (𝟙 T.left ≫ T.hom)
          (fun a => (Over.homMk (𝟙 T.left) rfl : Over.mk (𝟙 T.left ≫ T.hom) ⟶ T) ≫ lv a) :=
        tateAt_congr M.univ N' (Category.id_comp g).symm _ _ (fun a => by congr 1) h0
      exact (GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc M.X M.s M.univ T lv hadd hker hlin (𝟙 T.left) x'
        (x'.base (⊥ : PrimeSpectrum k')) (⊥ : PrimeSpectrum k') (by
          first
          | exact specializes_rfl
          | (rw [Scheme.id.base_apply])
          | (simp only [Scheme.Hom.id_apply]; exact specializes_rfl)
          | exact (Subsingleton.elim (α := PrimeSpectrum k) _ _) ▸ specializes_rfl)).1 h1
  obtain ⟨f, -, -⟩ := (HY T lv).1 hlv
  obtain ⟨u, hu⟩ : z ∈ Set.range g := by rw [hg]; rfl
  refine ⟨(f.left ≫ h).base u, ?_⟩
  have hf : f.left ≫ h ≫ π = g := by rw [hh]; exact Over.w f
  rw [← hu, ← hf]
  rfl

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem cls_lbPow_eq_nsmul {X : Scheme} {L : LB X} (hL : L.IsLB) (c : ℕ) (h : (Hecke.lbPow L c).IsLB) :
    cls (Hecke.lbPow L c) h = c • cls L hL := by
  refine (cls_linComb hL _ _ h).trans ?_
  simp [pull_id]

theorem isPIsog_pullMor {S S' : Scheme.{0}} {s : S ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s}
    {o₁ o₁' : Obj b N (f ≫ s)} (n : ObjMap o₁ o f) (n' : ObjMap o₁' o' f) {c : ℕ} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog c o o' ψ) : IsPIsog c o₁ o₁' (pullMor n.cart n'.cart ψ) := by
  obtain ⟨hc, hmon, hact, heta, ⟨hpol⟩, ψ', hmon', h1, h2⟩ := hψ
  haveI := hmon
  haveI := hmon'
  have hl := pullMor_left n.cart n'.cart ψ
  set pm := pullMor n.cart n'.cart ψ with hpm
  refine ⟨hc, isMonHom_pullMor _ _ _, ?_, ?_, ?_, pullMor n'.cart n.cart ψ', isMonHom_pullMor _ _ _,
    pullMor_comp_eq_pow _ _ _ _ _ h1, pullMor_comp_eq_pow _ _ _ _ _ h2⟩
  · intro c'
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (hact c')
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, reassoc_of% hl, reassoc_of% (n.act c'), n'.act, e]
  · intro x
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (heta x)
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, n'.eta, reassoc_of% (n.eta x), e]
  · have hsq : n.φ₂ ≫ sq2 ψ = sq2 pm ≫ n'.φ₂ := PIsogExt.isSquare_square_compatible_homs n.sq n'.sq hl.symm
    have hA : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hB : (o₁'.P.pull (sq2 pm)).IsLB := pull_isLB o₁'.isLB _
    have hX : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(cls_eq_iff hA hB).1 ?_⟩
    have e1 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB n.φ₂)).2 n.pol
    have e1' := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB n'.φ₂)).2 n'.pol
    have e0 : c • cls o.P o.isLB = pull (sq2 ψ) (cls o'.P o'.isLB) := by
      rw [← cls_lbPow_eq_nsmul o.isLB c hX, ← cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _)]
      exact (cls_eq_iff hX _).2 hpol
    rw [cls_pull o.isLB] at e1
    rw [cls_pull o'.isLB] at e1'
    rw [cls_lbPow_eq_nsmul o₁.isLB c hA, cls_pull o₁'.isLB, e1, e1', ← pull_comp, ← hsq, pull_comp, ← e0,
      map_nsmul]

theorem isogTarget_spMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X),
    CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  intro p _ D R _ b N M c k L _ _ j ξ ζ h
  obtain ⟨hs, o, o', ψ, ⟨m⟩, ⟨m'⟩, hψ⟩ := h
  obtain ⟨o₁, ⟨n⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o
  obtain ⟨o₁', ⟨n'⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o'
  have key : ∀ (w : Sp L ⟶ Sp R), spMap j ≫ ξ ≫ M.s = w →
      ∃ (a a' : Obj b N w) (φ : a.A ⟶ a'.A), Nonempty (ObjMap a M.univ (spMap j ≫ ξ)) ∧
        Nonempty (ObjMap a' M.univ (spMap j ≫ ζ)) ∧ IsPIsog c a a' φ := by
    intro w hw
    subst hw
    exact ⟨o₁, o₁', _, ⟨n.comp m⟩, ⟨n'.comp m'⟩, isPIsog_pullMor n n' hψ⟩
  obtain ⟨a, a', φ, ha, ha', hφ⟩ := key _ (Category.assoc _ _ _).symm
  exact ⟨by simp only [Category.assoc, hs], a, a', φ, ha, ha', hφ⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.TorusExt

theorem periods_of_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  intro R _ _ _ I hA D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hco E E' hE hW F _ _ _ hkey
  have hL := GlobalTheory.firstFiveLaws
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  letI := gtGroup D₁.toPre F
  letI := gtGroup D₂.toPre F
  letI : ∀ (D : DegPre R), AddCommGroup (GtPtF D F) := fun D => gtGroup D F
  let iota : ∀ {D : DegPre R}, D.TauBimult → D.X →+ GtPtF D F := fun {D} hB =>
    letI := gtGroup D F
    AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
      obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
      refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
      exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq : ∀ {D : DegPre R} (hB : D.TauBimult) (x : D.X) (g : GtPtF D F), GtPtF.IsIota x g ↔ g = iota hB x := by
    intro D hB x g
    exact ⟨fun h => isIota_unique h (exists_iota (F := F) hB x).choose_spec,
      fun h => h ▸ (exists_iota (F := F) hB x).choose_spec⟩
  have qk_nsmul : ∀ {D : DegPre R} (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k), k • p.g = iota hB p.y := by
    intro D hB k p
    obtain ⟨h, h₁, h₂⟩ := p.eq
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq hB _ _).1 h₂)
  let qkMk : ∀ {D : DegPre R} (hB : D.TauBimult) {k : ℕ} (y : D.X) (g : GtPtF D F), k • g = iota hB y → QkPt D F k :=
    fun {D} hB {k} y g h => ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq hB _ _).2 h⟩
  have hB₁ := D₁.tau_bimult
  have hB₂ := D₂.tau_bimult
  have inj₂ := GlobalTheory.IotaInj.main hL R I hA D₂ F
  have dv₁ := (gt_onto_divisible_kernel hL R I hA D₁ F).2.1

  obtain ⟨ex, ad, tor⟩ := GlobalTheory.T.torusExtensionMap_welldefined_additive_characters R D₁.toPre D₂.toPre b h hlin.2.1 (fun χ => (hco χ).imp fun _ hu => hu.1) F
  choose mf hmf hmu using ex
  let m : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' mf fun x x' => (isAdd_iff_eq _ _ _).1
    (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hmf x) (hmf x') (hmf _))
  have hm : ∀ x x', Act D₁.toPre D₂.toPre b h x x' ↔ x' = m x := fun x x' => ⟨hmu x x', fun e => e ▸ hmf x⟩

  have push : ∀ k : ℕ, 1 ≤ k → ∀ f₁ f₂, Tors U₁.toUnifPre F k f₁ → Tors U₂.toUnifPre F k f₂ → ∀ p : QkPt D₁.toPre F k,
      ∃ p' : QkPt D₂.toPre F k, p'.g = m p.g ∧ f₂ p' = f₁ p ≫ c ∧ GtPtF.IsIota p'.y (m (iota hB₁ p.y)) := by
    intro k hk f₁ f₂ hf₁ hf₂ p
    obtain ⟨p', e₁, e₂⟩ := hkey k hk p (f₁ p) ((hf₁.1 _ _).2 rfl) (m p.g) ((hm _ _).2 rfl)
    refine ⟨p', e₁, ((hf₂.1 _ _).1 e₂).symm, (isIota_iff_eq hB₂ _ _).2 ?_⟩
    rw [← qk_nsmul hB₂ p', e₁, ← map_nsmul, qk_nsmul hB₁ p]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F 1 le_rfl
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F 1 le_rfl
  have ex₁ : ∀ y, ∃ y', GtPtF.IsIota y' (m (iota hB₁ y)) := fun y => by
    obtain ⟨p', -, -, hp'⟩ := push 1 le_rfl f₁ f₂ hf₁ hf₂ (qkMk hB₁ y (iota hB₁ y) (one_smul _ _))
    exact ⟨p'.y, hp'⟩
  choose φ₀ hφ₀ using ex₁
  let φ : D₁.toPre.X →+ D₂.toPre.X := AddMonoidHom.mk' φ₀ fun y y' => inj₂ _ _ _ (hφ₀ (y + y'))
    ((isIota_iff_eq hB₂ _ _).2 (by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y')]))
  have hφ : ∀ y, GtPtF.IsIota (φ y) (m (iota hB₁ y)) := hφ₀
  refine ⟨φ, fun y g hg => ⟨m g, (hm _ _).2 rfl, ?_⟩, fun y => ?_⟩
  · rw [(isIota_iff_eq hB₁ _ _).1 hg]; exact hφ y
  refine GlobalTheory.KeyIota.eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F k hk
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F k hk
  have wp₁ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₁ F k hk
  have wp₂ := GlobalTheory.T.weilQk_pairing_existsUnique_torus hL R I hA D₂ F k hk
  have torp : ∀ p : QkPt D₁.toPre F k, f₁ p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U₁.toUnifPre.ext
    exact ((hf₁.1 p _).2 rfl w hw).1

  obtain ⟨gk, hgk⟩ := dv₁ k hk (iota hB₁ y)
  let p : QkPt D₁.toPre F k := ⟨y, gk, _, hgk, (isIota_iff_eq hB₁ _ _).2 rfl⟩
  obtain ⟨p', -, hpp', hp'⟩ := push k hk f₁ f₂ hf₁ hf₂ p
  have hyp' : p'.y = φ y := inj₂ _ _ _ hp' (hφ y)

  have h0 : k • torusPt D₁.toPre F (Additive.ofMul t) = iota hB₁ 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero, map_zero]
  let q : QkPt D₁.toPre F k := qkMk hB₁ 0 (torusPt D₁.toPre F (Additive.ofMul t)) h0
  have hq : IsTor t q.g := (isTor_iff _ _).2 (isTorusPtF_torusPt t)
  obtain ⟨q', hqg, hqq', hq'i⟩ := push k hk f₁ f₂ hf₁ hf₂ q
  have hq'0 : q'.y = 0 := inj₂ _ _ _ hq'i ((isIota_iff_eq hB₂ _ _).2 (by
    show m (iota hB₁ 0) = iota hB₂ 0
    simp only [map_zero]))
  have hq'tor : IsTor (t.comp (AddMonoidHom.toMultiplicative h)) q'.g := tor t q.g q'.g hq ((hm _ _).2 hqg)

  have ec := GlobalTheory.T.uniformizationEndomorphism_calculus hL R I hA D₁ A₁ G₁ hG₁ U₁ F E E E
  have adE := ec.2.1
  choose aEf haE huE using ec.1
  let aE : GtPtF D₁.toPre F →+ GtPtF D₁.toPre F := AddMonoidHom.mk' aEf fun x x' => (isAdd_iff_eq _ _ _).1
    (adE x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (haE x) (haE x') (haE _))
  have hqE0 : k • aE q.g = iota hB₁ 0 := by
    rw [← map_nsmul]
    show aE (k • torusPt D₁.toPre F (Additive.ofMul t)) = _
    simp only [h0, map_zero]
  let qE : QkPt D₁.toPre F k := qkMk hB₁ 0 (aE q.g) hqE0
  have hqEtor : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) qE.g := ec.2.2.1 t q.g qE.g hq (haE q.g)
  have hFu := (GlobalTheory.UT.functorial_of_unif R I hA D₁ A₁ G₁ hG₁ U₁).2 E E' hE
  have hqE : f₁ qE = f₁ q ≫ E.aA := ((hf₁.1 _ _).1 ((hFu.2 F).2.2 k hk q qE (f₁ q)
    (by show (0 : D₁.toPre.X) = E'.h 0; rw [map_zero]) (haE q.g) ((hf₁.1 _ _).2 rfl))).symm

  have w₁ := (hf₁.2.2.2.2 _ _ _).1 ((wp₁ qE p).2 (t.comp (AddMonoidHom.toMultiplicative E.h)) rfl hqEtor)
  rw [hqE, ← Category.comp_id (f₁ p)] at w₁
  have w₂ := (GlobalTheory.T.commutator_pairing_eq_of_mumford_bundle_iso _ A₁ A₂ A₁ c c E.aA (𝟙 _) hc hc E.homA inferInstance hW F _ k (f₁ q) (f₁ p)
    (torp q) (torp p) _).2 w₁
  rw [← hqq', ← hpp'] at w₂
  have w₃ := (hf₂.2.2.2.2 _ _ _).2 w₂
  have e := (wp₂ q' p').1.unique w₃ ((wp₂ q' p').2 _ hq'0 hq'tor)
  rw [hyp'] at e
  exact e.symm

end GlobalTheory.Mum.Two
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.exists_linear_section_opposite_congr_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  first | exact @GlobalTheory.LowFilt.exists_cell_section | exact GlobalTheory.LowFilt.exists_cell_section | (intros; apply GlobalTheory.LowFilt.exists_cell_section <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_ker_vec | exact GlobalTheory.LowFilt.IsOpp.exists_ker_vec | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_ker_vec <;> assumption)
end
end
