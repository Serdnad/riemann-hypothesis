module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TopForm

theorem derivation_eq_zero_of_jacobian {k B F : Type} [CommRing k] [CommRing B] [Field F]
    {D : ℕ} {α : k →+* B} (hα : α.IsStandardSmoothOfRelativeDimension D) {ω : Forms α D}
    (hω : IsFreeGen B ω) (g : Fin D → B) {J : B} (hJ : J • ω = dForm α g) (φ : B →+* F)
    (hJ0 : φ J ≠ 0) (δ : B → F) (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = φ x * δ y + φ y * δ x) (hc : ∀ c, δ (α c) = 0)
    (hg : ∀ a, δ (g a) = 0) (b : B) : δ b = 0 := by
  classical
  letI := α.toAlgebra
  letI : Algebra B F := φ.toAlgebra
  letI : Algebra k F := (φ.comp α).toAlgebra
  haveI : IsScalarTower k B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := φ.domain_nontrivial
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k B := hα
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := B)
  have hr : Module.finrank B Ω[B⁄k] = D := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := B) D)
  let e := Module.finBasisOfFinrankEq B Ω[B⁄k] hr
  let δ' : Derivation k B F := Derivation.mk'
    { toFun := δ
      map_add' := hadd
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, hmul]
        rw [show δ (algebraMap k B c) = 0 from hc c, mul_zero, add_zero, Algebra.smul_def]
        rfl }
    (fun x y => hmul x y)
  let ℓ := δ'.liftKaehlerDifferential
  have hℓ (x : B) : ℓ (KaehlerDifferential.D k B x) = δ x :=
    Derivation.liftKaehlerDifferential_comp_D δ' x
  let m : Matrix (Fin D) (Fin D) B := Matrix.of fun a c => e.repr (KaehlerDifferential.D k B (g a)) c
  have hsum (a : Fin D) : KaehlerDifferential.D k B (g a) = ∑ c, m a c • e c :=
    (e.sum_repr _).symm
  obtain ⟨c, hc'⟩ := hω.2 (exteriorPower.ιMulti B D e)
  have h1 : dForm α g = m.det • exteriorPower.ιMulti B D e := by
    rw [dForm_eq, ← alternating_map_sum_smul_eq_det_smul]
    exact congrArg _ (funext hsum)
  have h2 : J = m.det * c := by
    apply hω.1
    change J • ω = (m.det * c) • ω
    rw [hJ, h1, mul_smul]
    exact congrArg _ hc'.symm
  have h3 : (φ.mapMatrix m).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact hJ0 (by rw [h2, map_mul, h0, zero_mul])
  have h4 : (φ.mapMatrix m).mulVec (fun c => ℓ (e c)) = 0 := by
    funext a

    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hg a, ← hℓ, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h5 := Matrix.eq_zero_of_mulVec_eq_zero h3 h4
  have h6 : ℓ = 0 := e.ext fun c => congrFun h5 c
  rw [← hℓ, h6, LinearMap.zero_apply]

end GlobalTheory.TopForm

namespace GlobalTheory.CanonLB

open TopForm
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem spMap_fst_surjective_field (F : Type) [Field F] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom F F F).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal F) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem eq_zero_tangent_of_jacobian {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}
    {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type}
    [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i) (g : Fin D → Γ(Y, K.bundle.U i))
    (hJ : evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0) (w : Sp (DualNumber F) ⟶ Y)
    (hw : ⊤ ≤ w ⁻¹ᵁ K.bundle.U i)
    (hfst : spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = z)
    (hp : w ≫ p = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p)
    (hg : ∀ a, (evalPt w _ hw (g a)).snd = 0) : w = spMap (TrivSqZeroExt.inlHom F F) ≫ z := by
  classical
  have hU : IsAffineOpen (K.bundle.U i) := K.affine i
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let y0 : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  have hx : z y0 ∈ K.bundle.U i := hz (Set.mem_univ y0)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨K.bundle.U i, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, K.bundle.U i)), z y0 ∈ Y.basicOpen (t : Γ(Y, K.bundle.U i)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hU).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hU (t : Γ(Y, K.bundle.U i))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, K.bundle.U i))))
  have hVU : Y.basicOpen (t : Γ(Y, K.bundle.U i)) ≤ K.bundle.U i := Y.basicOpen_le _
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, K.bundle.U i)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen (Y.basicOpen (t : Γ(Y, K.bundle.U i))) := hU.basicOpen _
  generalize Y.basicOpen (t : Γ(Y, K.bundle.U i)) = V at hxt hVU h₂ hV
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := fun y _ => by
    obtain rfl : y = y0 := Subsingleton.elim _ _
    exact hxt
  have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun y _ => by
    obtain ⟨y', rfl⟩ := spMap_fst_surjective_field F y
    have := hzV (Set.mem_univ y')
    rw [← hfst] at this
    exact this
  have hinlV : ⊤ ≤ (spMap (TrivSqZeroExt.inlHom F F) ≫ z) ⁻¹ᵁ V := fun y _ =>
    hzV (Set.mem_univ _)
  have key : ∀ (y : Sp F ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ V),
      spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = y →
      ∀ b, (evalPt w V hwV b).fst = evalPt y V hy b := by
    rintro y hy rfl b
    exact (evalPt_spMap_comp _ w V hwV hy b).symm
  have hfstV := key z hzV hfst
  have hconst (c : k) : (evalPt w V hwV (algX p V c)).snd = 0 := by
    have e1 : evalPt w V hwV (algX p V c) = evalPt (w ≫ p) ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := evalPt_constFn p w V hwV c
    have key2 : ∀ (q : Sp (DualNumber F) ⟶ Sp k), q = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p →
        (evalPt q ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)).snd = 0 := by
      rintro q rfl
      rw [evalPt_spMap_comp _ (z ≫ p) ⊤ le_rfl le_rfl]
      simp
    rw [e1]
    exact key2 _ hp
  have hJV : evalPt z V hzV (K.jacobian i hVU fun a => resG Y hVU (g a)) ≠ 0 := by
    rw [show (K.jacobian i hVU fun a => resG Y hVU (g a)) =
        resG Y hVU (K.jacobian i le_rfl g) from (K.resG_jacobian i le_rfl hVU g).symm,
      evalPt_res z hVU hz hzV]
    exact hJ
  have hδ := derivation_eq_zero_of_jacobian h₂ ((K.isFrame i).res hV hVU).gen
    (fun a => resG Y hVU (g a)) (K.jacobian_smul_om i hV hVU _) (evalPt z V hzV) hJV
    (fun b => (evalPt w V hwV b).snd) (fun x y => by simp)
    (fun x y => by
      simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, hfstV]
      ring)
    hconst (fun a => by rw [evalPt_res w hVU hw hwV]; exact hg a)
  refine ext_evalPt hV hwV hinlV (RingHom.ext fun b => ?_)
  rw [evalPt_spMap_comp _ z V hzV hinlV]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfstV]
    rfl
  · rw [hδ b]
    rfl

end GlobalTheory.CanonLB
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

namespace GlobalTheory


open GlobalTheory.TopForm in
theorem CanonLB.exists_jacobian_evalPt_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  intro k _ Y p D _ K i F _ z hz
  by_contra hcon
  push_neg at hcon
  let Sm : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i)) :=
    Submodule.comap (K.coeff i le_rfl) (RingHom.ker (evalPt z _ hz))
  have hsub : Set.range (dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) (D := D)) ⊆ (Sm : Set _) := by
    rintro _ ⟨g, rfl⟩
    exact (RingHom.mem_ker).2 (hcon g)
  have hle : (⊤ : Submodule Γ(Y, K.bundle.U i) (FormsOn p D (K.bundle.U i))) ≤ Sm := by
    rw [← span_dForm (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (K.bundle.U i)) D]
    exact Submodule.span_le.2 hsub
  have hmem : resForm (le_rfl : K.bundle.U i ≤ K.bundle.U i) (K.om i) ∈ Sm := hle Submodule.mem_top
  have h1 : evalPt z _ hz (K.coeff i le_rfl (resForm le_rfl (K.om i))) = 0 :=
    (RingHom.mem_ker).1 hmem
  rw [K.coeff_om, map_one] at h1
  exact one_ne_zero h1

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

theorem tate_lev_surj : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  intro l _ M _ hroot n x hx
  choose r hr using hroot
  have key : ∀ (m : ℕ) (y : M), (r^[m] y) ^ l ^ m = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, hr]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun m => (r^[m] x) ^ l ^ n) fun m => ⟨?_, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, key, hx]
  · rw [← pow_mul, mul_comm, pow_mul, Function.iterate_succ_apply', hr]
  · rw [GlobalTheory.HTLat.Tate.lev_mk, key]

end GlobalTheory.Published
end

section

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Good

open scoped nonZeroDivisors

theorem exists_vAdd_ge {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℕ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w a) ∧ ∀ w ∈ S, (B : ℤ) ≤ vAdd w a := by
  classical
  let I : Ideal (𝓞 K) := ∏ w ∈ S, w.asIdeal ^ B
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0 : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hmem : algebraMap (𝓞 K) K r ∈
      (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) := by
    have e : (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [Equiv.refl_apply, neg_neg, zpow_natCast, I]
      rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
      simp [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [e]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hrI, rfl⟩
  refine ⟨_, ha0, fun w => ?_, fun w hw => ?_⟩
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg] at h
    split_ifs at h
    · exact le_trans (by positivity) h
    · exact h
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg, if_pos hw] at h
    exact h

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem exists_twist_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) :
    ∃ a : c.F, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) ∧ ∀ w, s.hi w ≤ (vAdd w a : ℝ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 c.F)) := s.finite_lo.toFinset ∪ s.finite_hi.toFinset
  let B : ℕ := ⌈∑ w ∈ S, (|s.lo w| + |s.hi w|)⌉₊
  have hB : ∀ w ∈ S, |s.lo w| + |s.hi w| ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => |s.lo w| + |s.hi w|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hw).trans (Nat.le_ceil _)
  obtain ⟨a, ha0, hpos, hS⟩ := exists_vAdd_ge S B
  refine ⟨a, ha0, fun w => ?_, fun w => ?_⟩
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := neg_abs_le (s.lo w)
      push_cast at h2
      linarith [abs_nonneg (s.hi w)]
    · have : s.lo w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_left _ (s.finite_lo.mem_toFinset.2 h))
      rw [this, add_zero]; exact_mod_cast hpos w
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := le_abs_self (s.hi w)
      push_cast at h2
      linarith [abs_nonneg (s.lo w)]
    · have : s.hi w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_right _ (s.finite_hi.mem_toFinset.2 h))
      rw [this]; exact_mod_cast hpos w

theorem cnorm_smul {ι : Type} [Fintype ι] (k : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (k • u) = ‖k‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have : ∑ i, ‖(k • u) i‖ ^ 2 = ‖k‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

section Abstract

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem lattice_transfer (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set V) = ⊤) :
    L'.FG ∧ Submodule.span K (L' : Set W) = ⊤ ∧ Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  let ψ : V →ₗ[𝓞 K] W :=
    { toFun := fun f => a⁻¹ • φ f
      map_add' := fun f f' => by rw [map_add (f := _), smul_add]
      map_smul' := fun m f => by
        rw [RingHom.id_apply, ← algebraMap_smul K m f, map_smul, ← algebraMap_smul K m (a⁻¹ • φ f),
          smul_smul, smul_smul, mul_comm] }
  have hle : L' ≤ L.map ψ := fun g hg => by
    refine ⟨a • φ.symm g, hout g hg, ?_⟩
    show a⁻¹ • φ (a • φ.symm g) = g
    rw [map_smul, φ.apply_symm_apply, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hFG' : L'.FG := by
    have := isNoetherian_of_fg_of_noetherian _ (hFG.map ψ)
    exact isNoetherian_submodule.mp this _ hle
  have hspan' : Submodule.span K (L' : Set W) = ⊤ := by
    have hsub : Submodule.span K (L : Set V) ≤ (Submodule.span K (L' : Set W)).comap (φ : V →ₗ[K] W) := by
      refine Submodule.span_le.2 fun f hf => Submodule.mem_comap.2 ?_
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    rw [eq_top_iff]
    intro g _
    have h := hsub (show φ.symm g ∈ Submodule.span K (L : Set V) by rw [hspan]; trivial)
    simpa using h
  refine ⟨hFG', hspan', ?_⟩
  unfold Formalism.HN.rkK
  rw [hspan, hspan', finrank_top, finrank_top]
  exact φ.symm.finrank_eq


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in
theorem hasGram_transfer (φ : V ≃ₗ[K] W) (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (h : ∀ σ f, N' σ (φ f) = t σ * N σ f) (hN : HasGram N) : HasGram N' := by
  obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hN
  refine ⟨⟨n, ⟨(b.map φ, fun v => ((t v.embedding : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
  have hk : ((t v.embedding : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (ht _).ne')
  have hdet := (hX v).1
  refine ⟨?_, fun y => ?_⟩
  · show IsUnit ((((t v.embedding : ℂ)⁻¹) • X v).det)
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
  · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t v.embedding : ℂ)⁻¹) • X v) v y = N' v.embedding y
    have := invertibleOfNonzero hk
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
    have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
    rw [hvec, Matrix.smul_mulVec, cnorm_smul, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
      ← φ.apply_symm_apply y, h, φ.apply_symm_apply]
    rw [inv_inv, Complex.norm_real, Real.norm_of_nonneg (ht _).le]

end Abstract

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem twist_goodOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G _hU hG hgood
  obtain ⟨hGram, hFG, hspan⟩ := hgood
  obtain ⟨φ, hφ, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := exists_twist_scalar s
  obtain ⟨hFG', hspan', hrk⟩ := lattice_transfer φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _)) hFG hspan
  refine ⟨⟨hasGram_transfer φ _ _ s.cInf s.cInf_pos (fun σ f => ?_) hGram, hFG', hspan'⟩, hrk⟩
  show petOn U x V dict Z (G + G₀) σ (φ f : Rul Xo c) = s.cInf σ * petOn U x V dict Z G σ (f : Rul Xo c)
  rw [hφ, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG _ f.2.2]

end GlobalTheory.FlatTw.Good
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.subMeanValue_flagChart_invariantMeasure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  first | exact @GlobalTheory.SubmeanChart.submean_chart | exact GlobalTheory.SubmeanChart.submean_chart | (intros; apply GlobalTheory.SubmeanChart.submean_chart <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.principalLevel_components_doubleCosets_congruence : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (g : (U σ).Comp → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (Λk : (U σ).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (u : (U σ).Comp → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ k, ((U σ).X k).Gm = G ∧ GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) G (g k) ∧ (Λk k : Set (Fin D.R.r → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (g k) (Λ : Set (Fin D.R.r → D.host.E)) ∧ (Λk k).FG ∧ Submodule.span D.host.E (Λk k : Set (Fin D.R.r → D.host.E)) = ⊤ ∧ (∀ τ ∈ ((U σ).X k).Ψ, gram τ G (u k τ) = G.map τ) ∧ (∀ γ ∈ ((U σ).X k).Γ, ∃ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) ∧ ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ γ' : GL (Fin D.R.r) D.host.E, (IsUStab G (Λk k) γ' ∧ ∀ x ∈ Λk k, ∃ y ∈ Λk k, (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec x - x = l.M • y) → ∃ γ ∈ ((U σ).X k).Γ, ∀ τ ∈ ((U σ).X k).Ψ, u k τ * (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * u k τ) ∧ ∀ k k', GlobalTheory.UCls.UEquiv (IsCMField.complexConj D.host.E) G (Λ : Set (Fin D.R.r → D.host.E)) l.M (g k) (g k') → k = k' := by
  first | exact @GlobalTheory.LevGeo.Reps.components_double_cosets | exact GlobalTheory.LevGeo.Reps.components_double_cosets | (intros; apply GlobalTheory.LevGeo.Reps.components_double_cosets <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_selfDual_data_transvection_principal_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  first | exact @GlobalTheory.LevGeo.exists_dataX_transv | exact GlobalTheory.LevGeo.exists_dataX_transv | (intros; apply GlobalTheory.LevGeo.exists_dataX_transv <;> assumption)
end
