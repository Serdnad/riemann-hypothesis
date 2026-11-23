module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle356
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open ReciprocityTheory.ChartRestriction.G.DVR (HasVal GenHasVal wchart_le_preimage)

noncomputable section

namespace GlobalTheory.QValPull

theorem chart_eq_of_val {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {φ : PUnit → (Spec (CommRingCat.of V) ⟶ X)} {φ' : PUnit → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ : ∀ k, φ' k = jK V ≫ φ k) {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (h : ∀ (z : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ X) → L.ι),
      Good L z J → (val t (𝟙 _) z J).val =
        gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) * (val e (𝟙 _ ≫ jK V) z J).val)
    (j : PUnit → L.ι) :
    (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val := by
  apply fn_ext
  intro x hx
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL x φ' j (fun a b _ => by cases a; cases b; rfl)
    (fun k => LB.wchart_le L φ' j k hx)
  have h1 : ∀ k, J (𝟙 _ ≫ φ' k) = j k := fun k => by rw [Category.id_comp]; exact hJj k
  have h2 : ∀ k, J ((𝟙 _ ≫ jK V) ≫ φ k) = j k := fun k => by rw [Category.id_comp, ← hφ]; exact hJj k
  have eL : gs (𝟙 _) x _ (t.s j).val = (val t (𝟙 _) x J).val :=
    (gs_unit _ x _ hx _).trans (congrArg Units.val (val_of t (𝟙 _) x J j h1).symm)
  rw [eL, h x J hJ]
  refine Eq.trans ?_ (gs_mul _ x _ hx _ _).symm
  congr 1
  · exact (gs_res _ x _ hx _).symm
  · have hx' : x ∈ LB.wchart L φ' j := hx
    have hxe : x ∈ jK V ⁻¹ᵁ LB.wchart L φ j := wchart_le_preimage L (jK V) φ φ' hφ j hx'
    unfold res pullU
    simp only [Units.coe_map, MonoidHom.coe_coe]
    refine Eq.symm ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 _) (jK V) x _ hxe _).trans
      ((gs_unit (𝟙 _ ≫ jK V) x _ hxe _).trans ?_)))
    exact congrArg Units.val (val_of e _ x J j h2).symm

theorem hasVal_fracMap {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] {g : V →+* V'}
    (hg : Function.Injective g) {ϖ : V} {ϖ' : V'} {e : ℕ} (ha : Associated (g ϖ) (ϖ' ^ e))
    {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) : HasVal ϖ' (ArcPull.fracMap hg c) (e * n) := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, hv⟩ := ha
  refine ⟨v⁻¹ ^ n * Units.map (g : V →* V') u, ?_⟩
  have hϖ : g ϖ = ϖ' ^ e * ((v⁻¹ : V'ˣ) : V') := by
    rw [← hv, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have key : ∀ (w : V'ˣ) (m : ℤ), algebraMap V' (FractionRing V') ((w ^ m : V'ˣ) : V') =
      algebraMap V' (FractionRing V') (w : V') ^ m := by
    intro w m
    have h1 := Units.coe_map (algebraMap V' (FractionRing V') : V' →* FractionRing V') (w ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    simpa only [MonoidHom.coe_coe] using h1.symm
  rw [map_mul, map_zpow₀, ArcPull.fracMap_algebraMap, ArcPull.fracMap_algebraMap, hϖ, Units.val_mul, map_mul,
    map_mul, map_pow, key, mul_zpow, ← zpow_natCast, ← zpow_mul]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem gs_scal_spMap {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (z : Spec (CommRingCat.of K')) (c : K) :
    gs (spMap f) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K))) c) =
      gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K'))) (f c)) := by
  unfold gs scal spMap
  simp only [TopologicalSpace.Opens.mem_top, ↓reduceDIte]
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hn]
  rfl

theorem qVal_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    {g : V →+* V'} {D : DegPre V} {D' : DegPre V'} (hD : IsPullDeg g D D') {ϖ : V} {ϖ' : V'} {e : ℕ}
    (hg : Function.Injective g) (ha : Associated (g ϖ) (ϖ' ^ e)) (y : D'.X) (n : ℤ) (h : QVal D ϖ (hD.xe y) n) :
    QVal D' ϖ' y (e * n) := by
  obtain ⟨e0, he0, c0, hc0, hch⟩ := h
  obtain ⟨e', he', hdown⟩ := ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (spMap g)
    (fun _ : PUnit => hD.c_pr y) e0 he0
  refine ⟨e', he', ArcPull.fracMap hg c0, hasVal_fracMap hg ha hc0, ?_⟩
  refine chart_eq_of_val D'.P.isLB (fun _ => DVR.QForm.ptK_eq D' y) ?_
  intro z J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB z (fun k : Empty => k.elim) (fun k : Empty => k.elim)
    (fun a => a.elim) (fun k => k.elim)
  have hv := DVR.SectionScalarValuation.val_genHasVal (hφ := fun _ => DVR.QForm.ptK_eq D (hD.xe y)) hch (ArcPull.genMap hg) z hJ
  have hp := ArcPull.psi_val hD (ArcPull.genMap hg) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) (ArcPull.fracMap_sq hg) hJ hJ' y
  have hd := hdown _ (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J J' hJ hJ'
  have hr : ArcPull.genMap hg ≫ jK V = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ spMap g := by
    rw [← ArcPull.fracMap_sq hg, Category.assoc]
    rfl
  have hxk : (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ (D'.c y).left := by
    rw [Category.assoc]
    exact congrArg _ (DVR.QForm.ptK_eq D' y)
  rw [hp, hr, hd] at hv
  simp only [Fintype.prod_unique, zpow_neg, zpow_one] at hv
  rw [← hxk, show ArcPull.genMap hg = spMap (ArcPull.fracMap hg) from rfl, gs_scal_spMap] at hv
  generalize ArcPull.om hD.w z J J' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = o at hv
  generalize val (D'.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z J' = A at hv ⊢
  generalize val e' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J' = E at hv ⊢
  generalize gs (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z ⊤ (scal (𝟙 _) (ArcPull.fracMap hg c0)) = G at hv ⊢
  rw [Units.val_mul, Units.val_mul] at hv
  linear_combination o.val * hv + (G * E.val - A.val) * Units.mul_inv o

theorem main : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D')
    (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' →
    Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  intro T T' g D D' hD ϖ ϖ' e hg _ _ ha y n h
  exact qVal_pull hD hg ha y n h

end GlobalTheory.QValPull
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PrimCentIdem

open CategoryTheory

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem eq_sum_single (e : MonoidAlgebra ℂ Γ) : e = ∑ q : Γ, MonoidAlgebra.single q (e.coeff q) := by
  classical
  ext x
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ Γ) (x : Γ) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

theorem exists_scalar (e : MonoidAlgebra ℂ Γ) (he : ∀ w, e * w = w * e) (ρ : FDRep ℂ Γ) [Simple ρ] :
    ∃ c : ℂ, ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v := by
  let T : ρ →ₗ[ℂ] ρ := ∑ q : Γ, e.coeff q • ρ.ρ q
  have hTA : T = Representation.asAlgebraHom ρ.ρ e := by
    conv_rhs => rw [eq_sum_single e]

    simp only [T, map_sum, Representation.asAlgebraHom_single]
  have hcomm : ∀ h : Γ, ∀ v : ρ, T (ρ.ρ h v) = ρ.ρ h (T v) := by
    intro h v
    have h1 : Representation.asAlgebraHom ρ.ρ (e * MonoidAlgebra.single h 1) = Representation.asAlgebraHom ρ.ρ (MonoidAlgebra.single h 1 * e) := by
      rw [he]
    rw [map_mul, map_mul, Representation.asAlgebraHom_single, one_smul] at h1
    rw [hTA]
    exact LinearMap.congr_fun h1 v
  let f' : ρ ⟶ ρ := ⟨FGModuleCat.ofHom T, fun g => by
    ext v
    exact hcomm g v⟩
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f'
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun φ : ρ ⟶ ρ => φ.hom.hom v) hc
  exact this.symm

theorem mul_zIdem_eq_smul (e : MonoidAlgebra ℂ Γ) (ρ : FDRep ℂ Γ) (c : ℂ)
    (hc : ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v) :
    e * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ = c • Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  ext x
  rw [coeff_mul_fin, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  have hT : (∑ q : Γ, e.coeff q • ρ.ρ q) = c • (1 : Module.End ℂ ρ) := LinearMap.ext fun v => by simp [hc v]
  have h1 : ∀ q : Γ, ρ.ρ (q⁻¹ * x)⁻¹ = ρ.ρ x⁻¹ * ρ.ρ q := fun q => by rw [mul_inv_rev, inv_inv, map_mul]
  have h2 : ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) =
      LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ∑ q : Γ, e.coeff q • ρ.ρ q) := by

    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  have h3 : ∑ q : Γ, e.coeff q * ((Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ ρ (ρ.ρ (q⁻¹ * x)⁻¹)) =
      (Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1]; ring
  rw [h3, h2, hT, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  ring

end GlobalTheory.PrimCentIdem

open GlobalTheory.PrimCentIdem in
theorem GlobalTheory.PrimCentIdem.main : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a),
    ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  intro g a _ L τ
  classical
  obtain ⟨hfin, hsum⟩ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one (GL (Fin a) (ZMod g))
  have hex : ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧
      L.idem τ * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply L.idem_ne τ
    rw [← mul_one (L.idem τ), ← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨ρ, hρ, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hz
    exact hno ρ hρ
  obtain ⟨ρ, hρ, hne⟩ := hex
  haveI := hρ
  refine ⟨ρ, hρ, ?_⟩
  set e := L.idem τ with he_def
  set z := Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ with hz_def
  have hzz : z * z = z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).1
  have hee : e * e = e := L.idem_idem τ
  have hec : ∀ w, e * w = w * e := L.idem_central τ
  have hzc : ∀ w, z * w = w * z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  obtain ⟨c, hc⟩ := exists_scalar e hec ρ
  have hmul : e * z = c • z := mul_zIdem_eq_smul e ρ c hc
  have hze : z * e = e * z := hzc e
  have hprim := L.idem_prim τ (e * z)
    (calc e * z * (e * z) = e * (z * e) * z := by simp only [mul_assoc]
      _ = e * (e * z) * z := by rw [hze]
      _ = (e * e) * (z * z) := by simp only [mul_assoc]
      _ = e * z := by rw [hee, hzz])
    (fun w => calc e * z * w = e * (z * w) := mul_assoc _ _ _
      _ = e * (w * z) := by rw [hzc w]
      _ = (e * w) * z := (mul_assoc _ _ _).symm
      _ = (w * e) * z := by rw [hec w]
      _ = w * (e * z) := mul_assoc _ _ _)
    (show e * z * e = e * z from calc e * z * e = e * (z * e) := mul_assoc _ _ _
      _ = e * (e * z) := by rw [hze]
      _ = (e * e) * z := (mul_assoc _ _ _).symm
      _ = e * z := by rw [hee])
  have hez : e * z = e := hprim.resolve_left hne
  have hcz : c • z ≠ 0 := hmul ▸ hne
  have hc0 : c ≠ 0 := fun h => hcz (by rw [h, zero_smul])
  have hz0 : z ≠ 0 := fun h => hcz (by rw [h, smul_zero])
  have hidem : (c * c - c) • z = 0 := by
    have h1 : (c • z) * (c • z) = c • z := by rw [← hmul, hez, hee]
    rw [smul_mul_smul_comm, hzz] at h1
    rw [sub_smul, h1, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.1 hidem).resolve_right hz0
  have hc1 : c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hcc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.1 h
  rw [← hez, hmul, hc1, one_smul]
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.JumpWin

theorem finset_of_rat (F : Finset ℚ) (n N : ℕ) (P : ℤ → Prop) (hF : F.card ≤ n)
    (hP : ∀ a, P a → (a : ℚ) ∈ F ∧ -(N : ℤ) ≤ a ∧ a ≤ N) :
    ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(N : ℤ) ≤ u ∧ u ≤ N) ∧ ∀ a, P a → a ∈ U := by
  classical
  refine ⟨(F.image fun q => ⌊q⌋).filter (fun u => -(N : ℤ) ≤ u ∧ u ≤ N), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hF)
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro a ha
    obtain ⟨h1, h2⟩ := hP a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a : ℚ), h1, Int.floor_intCast a⟩, h2⟩

variable {D : D7}

open AdmissibleParameterJ

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up <;> simp only [JW, cloudT, lowT, JJ, Jp, Jm, reflS, Bool.false_eq_true, if_true, if_false,
    Set.mem_union, Set.mem_setOf_eq] at hq ⊢ <;> tauto

theorem exists_finset_JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) :
    ∃ F : Finset ℚ, F.card ≤ D.R.r ∧ ∀ q ∈ JW D up j ρ, q ∈ F := by
  classical
  let cl : Finset ℚ := Finset.univ.image (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)
  let lw : Finset ℚ := Finset.univ.image (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)
  have hcard : (cl ∪ lw).card ≤ D.R.r := by
    have h1 : cl.card ≤ D.R.k - 1 := Finset.card_image_le.trans (by simp)
    have h2 : lw.card ≤ D.R.m := Finset.card_image_le.trans (by simp)
    have hk := D.R.m_add_three_le_k
    have : (cl ∪ lw).card ≤ cl.card + lw.card := Finset.card_union_le _ _
    simp only [Ranks.r]
    omega
  have hmem : ∀ q, q ∈ cloudJ D j ρ ∪ lowJ D j ρ → q ∈ cl ∪ lw := by
    intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  cases up
  · refine ⟨(cl ∪ lw).image (AdmissibleParameterJ.refl D), Finset.card_image_le.trans hcard, ?_⟩
    intro q hq
    have hq' : AdmissibleParameterJ.refl D q ∈ cloudJ D j ρ ∪ lowJ D j ρ := by
      simpa only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
        Set.mem_setOf_eq] using hq
    refine Finset.mem_image.2 ⟨AdmissibleParameterJ.refl D q, hmem _ hq', ?_⟩
    simp only [AdmissibleParameterJ.refl]; ring
  · refine ⟨cl ∪ lw, hcard, ?_⟩
    intro q hq
    exact hmem q (by simpa only [JW, cloudT, lowT, if_true] using hq)

theorem zero_not_mem_JW (L : SizeData₂ D) (hc : jcCondition L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hj2 ρ
  cases up
  · intro h
    simp only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
      Set.mem_setOf_eq] at h
    have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
    rcases h with h | h
    · have := hcl _ h
      simp only [AdmissibleParameterJ.refl] at this
      linarith
    · rcases hlow _ h with ⟨-, h'⟩ | ⟨h', -⟩
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
  · simpa only [JW, cloudT, lowT, if_true] using h0

theorem natAbs_le_of_mem_JJ (L : SizeData₂ D) (he : JumpAbsoluteBound L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    a.natAbs ≤ ⌊2 * L.sc.b⌋₊ := by
  have h1 := he.1 j hj1 hj2 ρ up _ ha
  have h2 : |((a : ℚ) : ℝ)| ≤ 2 * L.sc.b := by
    have := he.2.1; have := he.2.2.2; linarith
  apply Nat.le_floor
  have : ((a.natAbs : ℕ) : ℝ) = |((a : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]; exact h2

end GlobalTheory.JumpWin


open GlobalTheory.JumpWin AdmissibleParameterJ in
theorem GlobalTheory.jumps_WpO_T2O_window : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  intro D L ep hA _hb hc he hf i r ρ π hr hπ hdec w hw C τ M hM
  classical
  obtain ⟨g, ρ', -, -, hT⟩ := hA i r hr w hw C τ
  have hj := D.nd.j_range i
  have hW := hT ρ π hπ hdec
  generalize decide (TypeU D ep g) = up at hW
  obtain ⟨F, hFc, hFm⟩ := exists_finset_JW up (D.nd.j i) ρ'
  rcases hM with rfl | rfl
  · refine ⟨finset_of_rat F D.R.r (⌊2 * L.sc.b⌋₊ + 1) _ hFc ?_, ?_⟩
    · intro a ha
      have hq := ((hW a).1).1 ha
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' a (JW_sub_JJ up _ ρ' hq)
      refine ⟨hFm _ hq, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).1).1 h0
      exact zero_not_mem_JW L hc up _ hj.1 hj.2 ρ' (by simpa using this)
  · refine ⟨finset_of_rat (F.image fun q => -q - 1) D.R.r (⌊2 * L.sc.b⌋₊ + 1) _
      (Finset.card_image_le.trans hFc) ?_, ?_⟩
    · intro a ha
      have hq : -(a : ℚ) - 1 ∈ JW D up (D.nd.j i) ρ' := ((hW a).2.2.1).1 ha
      have hq' : (((-a - 1 : ℤ)) : ℚ) ∈ JW D up (D.nd.j i) ρ' := by push_cast; exact hq
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' _ (JW_sub_JJ up _ ρ' hq')
      refine ⟨Finset.mem_image.2 ⟨_, hFm _ hq, by ring⟩, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).2.2.1).1 h0
      exact (hf _ hj.1 hj.2 ρ').2.2.1 up (by simpa using this)

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Cyc

theorem exists_integral_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∃ χ : GQ l →* ℤ_[l]ˣ, (∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l])) ∧ Continuous χ ∧ ∀ (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → ∃ g ∈ GK K, χ g = u := by
  intro l _ P
  have hχ : IsCyc P.χQ := P.χQ_cyc
  obtain ⟨hn, hc, hK⟩ := cyc_basic l P.χQ hχ
  let f : GQ l →* ℤ_[l] :=
    { toFun := fun g => ⟨(P.χQ g : ℚ_[l]), (hn g).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (P.χQ (a * b) : ℚ_[l]) = (P.χQ a : ℚ_[l]) * (P.χQ b : ℚ_[l])
        rw [map_mul, Units.val_mul]) }
  have hf : Continuous f := hc.subtype_mk _
  refine ⟨f.toHomUnits, fun g => rfl, ?_, ?_⟩
  · rw [Units.continuous_iff]
    exact ⟨hf, hf.comp continuous_inv⟩
  · intro K s hs u hu
    have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
    obtain ⟨g, hg, hgu⟩ := exists_chi_eq K P.χQ hχ _ hu1
    have hG : g ∈ Gj K s := ((hK K g hg).1 s).2 (by
      rw [hgu]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow ((u : ℤ_[l]) - 1) s).2
        (Ideal.mem_span_singleton.2 hu)
      rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at this)
    refine ⟨g, IntermediateField.fixingSubgroup_antitone hs hG, ?_⟩
    exact Units.ext (Subtype.ext hgu)

end GlobalTheory.Cyc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.epsilonRoot_sub_one_isPseudoUniformizer_tilt : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m := by
  first | exact @GlobalTheory.WeakClosed.TiltUnif.main | exact GlobalTheory.WeakClosed.TiltUnif.main | (intros; apply GlobalTheory.WeakClosed.TiltUnif.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M), (∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U) → (∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) → Continuous Φ := by
  first | exact @GlobalTheory.WeakClosed.continuous_of_tail | exact GlobalTheory.WeakClosed.continuous_of_tail | (intros; apply GlobalTheory.WeakClosed.continuous_of_tail <;> assumption)
end
