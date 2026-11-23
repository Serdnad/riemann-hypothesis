module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLocus

theorem exists_ideal_locTriv_noeth (hG : GlobalFnsSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (F : LB B.left) (hF : F.IsLB) :
    ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) →
      ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧
        Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI := hB.smooth
  have hP := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom hF
  have hQ := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := TrivRep.exists_ideal (TrivRep.TrivOn B.hom F) (TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => TrivRep.loc_iff B.hom F h q

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_lift {Y T : Over S} (y : Y ⟶ T) :
    IsPullback (lift (fst A Y) (snd A Y ≫ y)).left (snd A Y).left (snd A T).left y.left := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  have e₁ : (lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom = (fst A Y).left := by
    rw [show pullback.fst A.hom T.hom = (fst A T).left from rfl, ← Over.comp_left, lift_fst]
  have big : IsPullback ((lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom) (snd A Y).left A.hom
      (y.left ≫ T.hom) := by
    have := IsPullback.of_hasPullback A.hom Y.hom
    rw [e₁, Over.w y]
    exact this
  exact IsPullback.of_right big (by rw [← Over.comp_left, lift_snd, Over.comp_left]) h₀

theorem exists_closed_locTriv_noeth (hG : GlobalFnsSt) {T : Over S} [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (F : LB (A ⊗ T).left) (hF : F.IsLB) :
    ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
      TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  obtain ⟨I, hI⟩ := TrivSubscheme.exists_idealSheaf (TrivSubscheme.LocTrivOver (snd A T).left F)
    TrivSubscheme.LocTrivOver.comp TrivSubscheme.locTrivOver_of_affine (fun U => by
      haveI := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ S := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A T).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth hG Γ(T.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hA t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun R g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI R g.hom _ _ _ h₃, TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((TrivSubscheme.triv_pull_iff _ _ _).trans (TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun Y y => ?_⟩
  rw [hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ y.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι y.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp z.left I.subschemeι)

variable {A} [GrpObj A]

theorem same_iff_locTriv (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {N N' : LB (A ⊗ T).left}
    (hN : Fam A N) (hN' : Fam A N') {F : LB (A ⊗ T).left} (hF : F.IsLB)
    (hc : cls F hF = cls N hN.isLB - cls N' hN'.isLB) (Y : Over S) (y : Y ⟶ T) :
    Same A N N' y y ↔ TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left := by
  let ψ := (lift (fst A Y) (snd A Y ≫ y)).left
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [e, p]
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hs : Same A N N' y y ↔ CechPic.pull ψ (cls F hF) = 0 := by
    rw [same_iff hN.isLB hN'.isLB, hc, map_sub, sub_eq_zero]
    rfl
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
      Triv (F.pull (r ≫ ψ)) ↔ CechPic.pull r (CechPic.pull ψ (cls F hF)) = 0 := fun r => by
    rw [← pull_comp, ← cls_pull hF _ (pull_isLB hF _)]
    exact (cls_eq_zero_iff (pull_isLB hF _)).symm
  have z₀ : CechPic.pull (e ≫ ψ) (cls F hF) = 0 := by
    have ee : e ≫ ψ = (lift (1 : Y ⟶ A) y).left := by
      simp only [e, ψ]
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [ee, hc, map_sub]
    have a := hN.add.evc_one hN.isLB y
    have b := hN'.add.evc_one hN'.isLB y
    simp only [evc] at a b
    rw [a, b, sub_zero]
  rw [TrivSubscheme.locTrivOver_iff (isPullback_lift A y), hs]
  constructor
  · intro h q
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩
  · intro h
    have cl : ∀ {Z : Scheme.{0}} (φ' : Fin 2 → (Z ⟶ (A ⊗ T).left)),
        Triv (LB.LinComb F φ' ![1, -1]) ↔
          CechPic.pull (φ' 0) (cls F hF) - CechPic.pull (φ' 1) (cls F hF) = 0 := fun φ' => by
      refine (cls_eq_zero_iff (LB.isLB_linComb hF _ _)).symm.trans ?_
      rw [cls_linComb hF, Fin.sum_univ_two]
      simp [sub_eq_add_neg]
    have sec : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
        CechPic.pull (r ≫ p ≫ e ≫ ψ) (cls F hF) = 0 := fun r => by
      rw [pull_comp, pull_comp, z₀, map_zero, map_zero]
    have T₀ : Triv (LB.LinComb F ![ψ, p ≫ e ≫ ψ] ![1, -1]) := by
      refine CubeGen.triv_of_local hF _ _ p e he (fun Z b U _ k => ?_) (fun V => ?_) (fun s => ?_)
      · have w : b ≫ e ≫ p ≫ e ≫ ψ = b ≫ e ≫ ψ := by
          rw [reassoc_of% he]
        simp [Fin.prod_univ_two, w]
      · let YV : Over S := Over.mk (V.ι ≫ Y.hom)
        let v : YV ⟶ Y := Over.homMk V.ι rfl
        exact ⟨_, _, (snd A YV).left, isPullback_lift A v, surj_snd hG hA YV⟩
      · obtain ⟨U, hU, ht⟩ := h s
        refine ⟨U, hU, ?_⟩
        unfold CubeGen.TrivAt
        rw [cl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sec, sub_zero, pull_comp]
        exact (key _).1 ht
    have := (cl _).1 T₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    have s₁ := sec (𝟙 _)
    rw [Category.id_comp] at s₁
    rwa [s₁, sub_zero] at this

theorem exists_closed_same : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left],
    IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T),
      IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  intro S A T _ _ hA N N' hN hN'
  obtain ⟨F, hF, hc⟩ := cls_surj (cls N hN.isLB - cls N' hN'.isLB)
  obtain ⟨G, i, hi, hG⟩ := exists_closed_locTriv_noeth A ExpansionTotal.globalFns hA F hF
  exact ⟨G, i, hi, fun Y y => (same_iff_locTriv ExpansionTotal.globalFns hA hN hN' hF hc Y y).trans (hG Y y)⟩

end GlobalTheory.DualLocus
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll


open GlobalTheory.CMModel.LocAll in
theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.LatMatch

section Abstract
variable {R : Type} [CommRing R] [Nontrivial R]

theorem card_eq_of_inv {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin a) R)
    (h1 : A * B = 1) (h2 : B * A = 1) : a = b := by
  let e : (Fin b → R) ≃ₗ[R] (Fin a → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

end Abstract

theorem nontrivial_R (D : D7) : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  exact (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective).nontrivial



theorem frames_match_lattices : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' n hF Q Q' hQ hQ' P e f hP
  haveI := nontrivial_R D
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, hU⟩ := hQ
  obtain ⟨⟨γ, γ', hc1, hc2, hK'⟩, hU'⟩ := hQ'
  have hr : V.rank = n := card_eq_of_inv β β' hb1 hb2
  have hr' : V'.rank = n := card_eq_of_inv γ γ' hc1 hc2
  refine ⟨hr'.trans hr.symm, ?_⟩
  let X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := γ * β'
  let X' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := β * γ'
  have hX1 : X * X' = 1 := by
    show γ * β' * (β * γ') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β' β γ', hb2, Matrix.one_mul, hc1]
  have hX2 : X' * X = 1 := by
    show β * γ' * (γ * β') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, hb1]
  have hconj : ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * X = X * finMat D.sp.cm.sig V.gram (Q.ψ κ) := by
    intro κ
    rw [hK' κ, hK κ]
    show _ * (γ * β') = γ * β' * _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hff : f * f = f := (T3 P e f hP).1
  set φ := finPart D f with hφdef
  have hφ : φ * φ = φ := by rw [hφdef, ← map_mul, hff]
  have hφint : φ ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D φ hφ
  have sm : ∀ (W : HSp D), ∀ a ∈ intAE D, ∀ y ∈ Formalism.L2.NTheta.LamHat W, a • y ∈ Formalism.L2.NTheta.LamHat W :=
    fun W a ha y hy => GlobalTheory.LatDual.smul_mem_lamHat W a ha y hy
  have nsm : ∀ (W : HSp D) (N : ℕ), ∀ y ∈ Formalism.L2.NTheta.LamHat W, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • y ∈ Formalism.L2.NTheta.LamHat W := by
    intro W N y hy
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hy N
  obtain ⟨N1, hN1, hB1⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V V' X
  obtain ⟨N2, hN2, hB2⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V' V X'
  let hom : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :=
    (DistribSMul.toAddMonoidHom _ φ).comp (Matrix.mulVecLin X).toAddMonoidHom
  have hhom : ∀ y, hom y = φ • X.mulVec y := fun y => rfl
  let M : AddSubgroup (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := (Formalism.L2.NTheta.LamHat V).map hom
  have hM : ∀ z, z ∈ M ↔ ∃ y ∈ Formalism.L2.NTheta.LamHat V, φ • X.mulVec y = z := fun z => by
    simp only [M, AddSubgroup.mem_map, hhom]
  have c1 : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M := by
    intro a ha z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    refine (hM _).2 ⟨a • y, sm V a ha y hy, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm]
  have c2 : ∀ z ∈ M, φ • z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    rw [smul_smul, hφ]
  have c3 : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V', ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • y) ∈ M) ∧
      ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V' := by
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun y hy => ?_, fun z hz => ?_⟩
    · refine (hM _).2 ⟨((N1 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (((N2 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X'.mulVec y), nsm V N1 _ (hB2 y hy), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hX1, Matrix.one_mulVec]
      simp only [smul_smul, Nat.cast_mul]
      congr 1
      ring
    · obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
      have h1 := nsm V' N2 _ (sm V' φ hφint _ (hB1 y hy))
      convert h1 using 1
      simp only [Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
  have c4 : ∀ g : GA D V', g ∈ KsphC V' ∅ → SuppF V' f g → ∀ z ∈ M,
      (finMat D.sp.cm.sig V'.gram g).mulVec z ∈ M := by
    intro g hg _ z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    obtain ⟨κ, hκ⟩ := Q'.onto g hg.1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hU' κ).2 (by rw [hκ]; exact hg)
    have hk : Q.ψ κ ∈ KsphC V ∅ := (hU κ).1 hκU
    refine (hM _).2 ⟨(finMat D.sp.cm.sig V.gram (Q.ψ κ)).mulVec y, (hk.2.1 y).1 hy, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj κ, hκ]
  have hcore : ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (φ • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V') := by
    rcases hP with ⟨hI, hfe⟩ | ⟨hfe, hpl, hint⟩
    · have h := GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple V' P e hI M
      rw [← hfe] at h
      exact h c1 c2 c3 c4
    · rw [← hfe] at hpl hint
      exact GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple V' P f hpl hint M c1 c2 c3 c4
  obtain ⟨c, ⟨u, rfl⟩, hcM⟩ := hcore
  refine ⟨(u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X, (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, Matrix.mul_smul X (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', smul_smul, hX1, Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', Matrix.mul_smul X' (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, smul_smul, hX2, Units.inv_mul, one_smul]
  · intro κ
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj κ]
  · intro y
    have e1 : φ • (((u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X).mulVec y) = (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • X.mulVec y) := by
      rw [Matrix.smul_mulVec, smul_comm]
    rw [e1]
    constructor
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hM _).2 ⟨φ • y, h, by rw [Matrix.mulVec_smul, smul_smul, hφ]⟩
      exact ((hcM _).1 hz).2
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hcM _).2 ⟨by rw [smul_smul, hφ], h⟩
      obtain ⟨y', hy', hyy⟩ := (hM _).1 hz
      have := congrArg X'.mulVec hyy
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX2,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      rw [← this]
      exact sm V φ hφint y' hy'

end GlobalTheory.LatMatch
end
end
