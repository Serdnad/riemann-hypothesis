module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHS.BridgeValue

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (P P' : FrPt Xo c S) (e : P'.x = P.x) : ∃ u : Sˣ, ∀ i, (e ▸ P'.s).f i = scal P.x (u : S) i * P.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  exact gen_unit P.s s' P.gen t4'

end GlobalTheory.CompHS.BridgeValue

namespace GlobalTheory.CompHS.BridgeValue

theorem val_sec₀_eq_evR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ W hW i φ x hx hz fr hfr ψ y hψ hm g hO hi
  let k := i PUnit.unit
  let ψ' : Γ(Y₀ TF.X Z, W) →+* CAt σ := ψ
  let q : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.X.YY := (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z
  let z' : Sp (CAt σ) ⟶ TF.X.YY := spMap ψ' ≫ q
  have hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hO' : ⊤ ≤ z' ⁻¹ᵁ flagOpen TF.X := fun s hs => hO hs
  have hpt : AllWt.ptF y = GlobalTheory.FlagMod.frX y := rfl
  have ex : spMap ψ' ≫ (x ≫ genι TF.Y) = z' ≫ TF.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ TF.Y.j = z' ≫ TF.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ TF.Y.j = (AllWt.ptF y ≫ TF.Y.jQ) ≫ genι TF.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ' ≫ (x ≫ genι TF.Y) := by rw [hm.1, Category.assoc]
    _ = z' ≫ TF.X.π := ex
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec TF.Y y hxy τ j = GlobalTheory.FlagMod.frVec TF.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← TF.X.F.tanPull_vecAt k ψ' q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := TF.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q y eQ
  let t : Ix Dw → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  have ht : FrBor t Q y := GlobalTheory.FlagMod.frBor_of_frVec (TF.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => by
      rw [hv τ j]
      refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j' j • _ = 0
        rw [Matrix.one_apply_ne hj', zero_smul]
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j j • _ = _
        rw [Matrix.one_apply_eq, one_smul]) (fun _ => hu0)
  have he := evR_eq_val_secOf (X := TF.X) g hO' hQ ht
  have hprod : (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix) = 1 := by
    rw [Fintype.prod_option, GlobalTheory.FlagMod.exOf_none, zpow_zero, _root_.one_mul]
    exact Finset.prod_eq_one fun _ _ => one_zpow _
  rw [hprod, Units.val_one, _root_.one_mul] at he
  have key : ∀ (a b : Sp (CAt σ) ⟶ TF.X.YY), a = b → ∀ hOa hia hOb hib,
      H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) a k hOa hia (secOf TF.X _ g) =
        H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) b k hOb hib (secOf TF.X _ g) := by
    intro a b hab; subst hab; intros; rfl
  refine (H0.val_pull (inc₀ TF.X Z) le_rfl _ i hO hi (fun s hs => hO' hs) (fun s hs => hz' hs) _).trans ?_
  refine (key _ _ (Category.assoc _ _ _) _ _ hO' hz').trans ?_
  exact he.symm

end GlobalTheory.CompHS.BridgeValue
end

section

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

def ArcZero (X : FlagCover Y) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ)
    (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)) : Prop :=
  ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι), W ≤ (L₀ X Z la).U i →
    ∀ (ψ : ℂ → (Γ(Y₀ X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r →
      (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z =
        spMap σ) →
      (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) s ∈ bd₀ X Z) →
      (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 →
        ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z)
          (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i),
          ‖H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hi m‖ < ε

end GlobalTheory.CompHS
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem appLE_comp_cst {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (U : W.Opens) (A : W'.Opens) (h : A ≤ π ⁻¹ᵁ U) :
    (π.appLE U A h).hom.comp (cst f U) = cst (π ≫ f) A := by
  have e : f.appTop ≫ W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.appLE U A h =
      (π ≫ f).appTop ≫ W'.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
    simp [Scheme.Hom.appLE]
  ext r
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem cst_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (U : W.Opens) :
    cst (p ≫ Spec.map (CommRingCat.ofHom φ)) U = (cst p U).comp φ := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem comap_baseIdeal {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (J : Ideal R) : (baseIdeal f J).comap π = baseIdeal (π ≫ f) J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : W.affineOpens × W'.affineOpens // p.2.1 ≤ π ⁻¹ᵁ p.1.1}) (fun i => i.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ (π x)))
    obtain ⟨A, hA, hxA, hAU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 W'.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U.1 from hxU)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, ⟨A, hA⟩), hAU⟩, hxA⟩
  · intro i
    rw [GlobalTheory.Principalise.comapIdealAffine _ π i.1.1 i.1.2 i.2, baseIdeal_ideal, baseIdeal_ideal, Ideal.map_map,
      appLE_comp_cst]

theorem baseIdeal_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R) :
    baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ) := by
  rw [baseIdeal, baseIdeal, Ideal.map_map, cst_comp_specMap]

theorem mem_support_baseIdeal {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (J : Ideal R) (x : W) : x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
  have key : ∀ r, x ∈ W.basicOpen (cst f U.1 r) ↔ r ∉ (f x).asIdeal := by
    intro r
    simp only [cst, rs, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    simp only [hxU, TopologicalSpace.Opens.mem_inf, true_and]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, baseIdeal_ideal]
  unfold Ideal.map
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h r hr
    by_contra hn
    exact h _ ⟨r, hr, rfl⟩ ((key r).2 hn)
  · rintro h _ ⟨r, hr, rfl⟩ hx
    exact (key r).1 hx (h hr)

theorem baseIdeal_calculus :
    (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) :=
  ⟨fun _ _ _ _ f π J => comap_baseIdeal f π J,
    fun _ _ _ _ φ _ p J => baseIdeal_comp_specMap φ p J,
    fun _ _ _ f J x => mem_support_baseIdeal f J x⟩

end GlobalTheory.FormalAlg
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exact_clAll_toHO1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hc : Closed1 (OAff s) = ⊤) :
    Function.Exact (clAll (OAff s) hc) (toHO1 s) := by
  rw [LinearMap.exact_iff]
  change Fil1 (OAff s) = _
  rw [Fil1_eq_range, clAll, LinearMap.range_comp_of_range_eq_top]
  exact LinearEquiv.range _

theorem surjective_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) : Surjective f := by
  have : Surjective (e ≫ f) := by rw [he]; infer_instance
  exact Surjective.of_comp e f

theorem baseChange_HH1_globForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R _ A _ g hab hsm R' _ _ X' s' φ h
  obtain ⟨inst', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_of_isPullback_spMap' R A g hab hsm R' (algebraMap R R') X' s' φ h
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hab hsm
  obtain ⟨hfr', h0', -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R' (Over.mk s') g hab' hsm'
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hab hsm
  have hc' := GlobalTheory.T.abelianScheme_globalOneForms_closed R' (Over.mk s') g hab' hsm'
  have hflat : Flat s' := by
    haveI := hsm'
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth g s'
    infer_instance
  have hsurj : Surjective s' := by
    refine surjective_of_section s' (η[Over.mk s']).left ?_
    have := Over.w (η[Over.mk s'])
    simpa using this
  have hW := GlobalTheory.T.exists_equiv_globalOneForms_baseChange R R' A.left X' A.hom s' φ h hfr h0 hfr' h0' hflat hsurj
  refine ⟨?_, hW⟩
  have hH := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hab hsm).2.2.1 R' X' s' φ h
  refine GlobalTheory.T.semilinear_short_exact_compatible R R' (GlobForm A.hom) (HH1 A.hom) (HO1 A.hom) (GlobForm s') (HH1 s') (HO1 s')
    (clAll (OAff A.hom) hc) (toHO1 A.hom) (clAll (OAff s') hc') (toHO1 s')
    (pullForm h.w) (pullHH1 h.w) (pullHO1 h.w)
    (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hab hsm) (exact_clAll_toHO1 A.hom hc) ?_ (exact_clAll_toHO1 s' hc') ?_ ?_ hW hH
  · exact (ofForm_injective_of_H0Const R' _ (OAff s') h0').comp (LinearEquiv.injective _)
  · intro x
    exact GlobalTheory.T.pull_closed_form_class R R' A.left X' A.hom s' (algebraMap R R') φ h.w hc hc' x
  · intro x
    exact toHO1_pullHH1 h.w x

end GlobalTheory.AbCoh
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSRep

open MvPolynomial

theorem aeval_smul_of_hom {σ K : Type} [CommRing K] {d : ℕ} {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous d)
    (c : K) (y : σ → K) : aeval (c • y) P = c ^ d * aeval y P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hP (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem rep_of_trace {K : Type} [Field K] [CharZero K] {D : ℕ} (x : Fin (D + 1) → K) (hx0 : x 0 ≠ 0)
    [FiniteDimensional (ratF x) K] (g : Fin (Module.finrank (ratF x) K) → K) (hg : LinearIndependent (ratF x) g) :
    ∃ w : Fin (Module.finrank (ratF x) K) → K, ∀ (N : ℕ) (f : K)
      (T : Fin (Module.finrank (ratF x) K) → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous N) →
      (∀ i, (Algebra.trace (ratF x) K (f * g i / x 0 ^ N) : K) = aeval (fun l => x l / x 0) (T i)) →
      f = ∑ i, aeval x (T i) * w i := by
  classical
  haveI : Nonempty (Fin (Module.finrank (ratF x) K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hg (by simp)
  have hB : (Algebra.traceForm (ratF x) K).Nondegenerate := traceForm_nondegenerate _ _
  refine ⟨fun i => (Algebra.traceForm (ratF x) K).dualBasis hB b i, ?_⟩
  intro N f T hT htr
  have key := ((Algebra.traceForm (ratF x) K).dualBasis hB b).sum_repr (f / x 0 ^ N)
  simp_rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at key
  have hxN : x 0 ^ N ≠ 0 := pow_ne_zero _ hx0
  have hf : f = (f / x 0 ^ N) * x 0 ^ N := by field_simp
  rw [hf, ← key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbi : b i = g i := by simp [b]
  have hx : x = x 0 • fun l => x l / x 0 := by
    funext l; simp [smul_eq_mul, mul_div_cancel₀ _ hx0]
  rw [Algebra.smul_def, hbi, div_mul_eq_mul_div, show (algebraMap (ratF x) K) (Algebra.trace (ratF x) K (f * g i / x 0 ^ N)) = _ from htr i]
  have hT' : aeval x (T i) = x 0 ^ N * aeval (fun l => x l / x 0) (T i) := by
    conv_lhs => rw [hx]
    exact aeval_smul_of_hom (hT i) _ _
  rw [hT']
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [← norm_val]; exact norm_nonneg _

theorem sections_eq_sum_aeval_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (w : Fin (Module.finrank (ratF x) X.functionField) → X.functionField) (C : ℝ), 0 < C ∧ ∀ (q : ℕ), ∀ f ∈ P.H (e * q + a) b, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i ∧ ∀ R κ : ℝ, 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * q + a) b σ y f ≤ R) → ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ C * R / κ ^ (q + c) := by
  intro k _ X _ p D hV P hA e x hG a b
  classical
  obtain ⟨hx0s, hai, hfd⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hV P hA e x hG
  haveI := hfd
  obtain ⟨hch, -⟩ := GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hV
  haveI := hch
  set n' := Module.finrank (ratF x) X.functionField with hn'
  obtain ⟨c0, g0, hg0, hli0⟩ := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hV P hA e x hG (-a) (-b)

  have hli : LinearIndependent (ratF x) (fun i => g0 i * x 0) := by
    have hk : LinearMap.ker (LinearMap.mulRight (ratF x) (x 0)) = ⊥ :=
      LinearMap.ker_eq_bot.2 (mul_left_injective₀ (hx0s 0))
    have := hli0.map' (LinearMap.mulRight (ratF x) (x 0)) hk
    exact this
  have hgH : ∀ i, (fun j => g0 j * x 0) i ∈ P.H (e * c0 + -a + e) (-b + 0) := fun i =>
    (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hg0 i) (hG.mem 0)).1
  generalize hgdef : (fun j => g0 j * x 0) = g at hli hgH
  obtain ⟨w, hw⟩ := rep_of_trace x (hx0s 0) g hli

  have hbd : ∀ i, ∃ Ci : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Ci :=
    fun i => ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hV P _ _).2 _ (hgH i)).2
  choose Ci hCi using hbd
  set Cg : ℝ := ∑ i, |Ci i| + 1 with hCg
  have hCg1 : 1 ≤ Cg := by
    have : 0 ≤ ∑ i, |Ci i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hCgi : ∀ i σ y, P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Cg := fun i σ y => by
    have h1 : Ci i ≤ |Ci i| := le_abs_self _
    have h2 : |Ci i| ≤ ∑ j, |Ci j| := Finset.single_le_sum (f := fun j => |Ci j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [hCi i σ y]
  have hn'pos : (0 : ℝ) < n' := by exact_mod_cast Module.finrank_pos
  refine ⟨c0 + 1, w, n' * Cg, by positivity, ?_⟩
  intro q f hf
  set N := q + (c0 + 1) with hNdef
  have hN1 : 1 ≤ N := by omega
  have hidx : ((e : ℤ) * q + a) + (e * c0 + -a + e) = (N : ℤ) * e := by rw [hNdef]; push_cast; ring
  have hidx2 : b + (-b + 0) = (N : ℤ) * 0 := by ring
  have hu : ∀ i, f * g i ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (f * g i) =
        P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := fun i => by
    have := NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ f (g i) hf (hgH i)
    rw [hidx, hidx2] at this
    exact this
  have hxpow : ∀ l, x l ^ N ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (x l ^ N) = P.nu e 0 σ y (x l) ^ N := fun l =>
    NuPow.pow_mem_H_and_nu_pow k X p P _ _ (x l) (hG.mem l) N
  have hnv : ∀ l, NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x l ^ N) = NV P e 0 (x l) := fun l =>
    (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hG.mem l)).2.2.1 N hN1
  have hreg : ∀ i l, ∀ z ∈ NV P e 0 (x l), RegAt z (f * g i / x l ^ N) := fun i l z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x l ^ N) (hxpow l).1).2.2.2.1 _ (hu i).1 z (by rw [hnv l]; exact hz)).1
  have hintg : ∀ i l, IsIntegral (ratR x l) (f * g i / x l ^ N) := fun i l =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG l _ (hx0s l) (hreg i l)
  have hTex : ∀ i, ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous N ∧
      (Algebra.trace (ratF x) X.functionField (f * g i / x 0 ^ N) : X.functionField) = aeval (fun l => x l / x 0) T :=
    fun i => GlobalTheory.T.exists_homogeneous_int_trace_sectionTuple X.functionField D x hx0s hai hfd N (f * g i) (hintg i)
  choose T hT htr using hTex
  refine ⟨T, hT, hw N f T hT htr, ?_⟩
  intro R κ hκ hcov hR i α
  obtain ⟨U, hgen, hU, -, hregU, -, -, hpts⟩ := GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hV P hA e (x 0) hG.pos (hG.mem 0) (hx0s 0)
  have hB : ∀ l, x l / x 0 ∈ (fnOf U hgen).range := fun l => (hregU _).1 fun z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.1 _ (hG.mem l) z (by rw [← hU]; exact hz)).1
  have hBint : ∀ b' ∈ (fnOf U hgen).range, IsIntegral (ratR x 0) b' := fun b' hb =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG 0 b' (hx0s 0) fun z hz => (hregU b').2 hb z (show z ∈ (U : Set X) by rw [hU]; exact hz)
  have hwB : f * g i / x 0 ^ N ∈ (fnOf U hgen).range := (hregU _).1 fun z hz => hreg i 0 z (by rw [← hU]; exact hz)
  have key := GlobalTheory.T.norm_aeval_traceForm_le_fibreValues X.functionField D x hx0s hai hfd (fnOf U hgen).range hB hBint ⟨_, hwB⟩ (T i) (htr i)
  have hcoef := GlobalTheory.T.abs_coeff_le_of_homogeneous_torus_bound D N (T i) (n' * (R * Cg / κ ^ N)) (hT i) ?_ α
  · exact le_of_le_of_eq hcoef (by ring)
  intro z hz0 hz1
  refine key z _ hz0 fun φ hφ => ?_
  obtain ⟨σ, y, hyU, hval⟩ := hpts φ
  have hyNV : under y ∈ NV P e 0 (x 0) := by rw [← hU]; exact hyU
  obtain ⟨l, hl⟩ := hcov σ y
  have h5 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.2 (x l) (hG.mem l) σ y hyNV
  have hzl : ‖ratVal (x l / x 0) y‖ = 1 := by
    have := hval ⟨_, hB l⟩
    simp only at this
    rw [this, hφ l, hz1 l]
  have hx0κ : κ ≤ P.nu e 0 σ y (x 0) := by rw [h5.1, hzl, one_mul] at hl; exact hl
  have hyN : under y ∈ NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x 0 ^ N) := by rw [hnv 0]; exact hyNV
  have h6 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x 0 ^ N) (hxpow 0).1).2.2.2.2 (f * g i) (hu i).1 σ y hyN
  rw [(hu i).2, (hxpow 0).2] at h6
  have hv := hval ⟨_, hwB⟩
  simp only at hv
  rw [← hv, le_div_iff₀ (pow_pos hκ N)]
  calc ‖ratVal (f * g i / x 0 ^ N) y‖ * κ ^ N ≤ ‖ratVal (f * g i / x 0 ^ N) y‖ * P.nu e 0 σ y (x 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ.le hx0κ N) (norm_nonneg _)
    _ = P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := h6.1.symm
    _ ≤ R * Cg := mul_le_mul (hR σ y) (hCgi i σ y) (nu_nonneg _ _ _ _ _ _) (le_trans (nu_nonneg _ _ _ _ _ _) (hR σ y))

end GlobalTheory.HSRep
end
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.nonempty_definiteRationalPointData_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) := by
  first | exact @GlobalTheory.DefPt.PtExist.main | exact GlobalTheory.DefPt.PtExist.main | (intros; apply GlobalTheory.DefPt.PtExist.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_global_harmonic_congr_column_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  first | exact @GlobalTheory.RefGlob.exists_harmA_congr_polyT | exact GlobalTheory.RefGlob.exists_harmA_congr_polyT | (intros; apply GlobalTheory.RefGlob.exists_harmA_congr_polyT <;> assumption)
end
