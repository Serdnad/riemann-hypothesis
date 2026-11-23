module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle258
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
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
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.Mem

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RayOnto

theorem containsRayField_comp {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

theorem exists_finset_containsRayField : GlobalTheory.NT.RayField → ∀ (P : Pre) (M : ℕ), M ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (φ : P.host.K →+* L), σ.comp φ = P.host.φ₀.comp (algebraMap P.host.K P.host.E) → (∀ z ∈ S, ∃ x, σ x = z) → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ M := by
  intro hR P M hM
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro L _ _ σ φ hσφ hS
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := GlobalTheory.Mem.Fld.algOf φK Rf hm
    obtain ⟨hab, hun, -, hart⟩ := hray
    haveI : IsGalois P.host.K Rf := hab.toIsGalois
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M :=
      GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun
        (fun I hI hc hχ => (hart I hI hc).1 hχ)
    have hle : Rf ≤ σ.toRatAlgHom.fieldRange := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      refine sum_mem fun i _ => IntermediateField.smul_mem _ ?_
      obtain ⟨y, hy⟩ := hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨y, hy⟩
    let e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField σ.toRatAlgHom
    let τ : Rf →+* L := (e.symm : σ.toRatAlgHom.fieldRange →+* L).comp
      (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)
    have key : ∀ w, σ (e.symm w) = (w : ℂ) := fun w => by
      conv_rhs => rw [← e.apply_symm_apply w]
      rfl
    have hτ : τ.comp (algebraMap P.host.K Rf) = φ := by
      ext x
      apply σ.injective
      have h1 : σ (φ x) = φK x := RingHom.congr_fun hσφ x
      rw [h1]
      exact key _
    rw [← hτ]
    exact containsRayField_comp _ τ M hc

end GlobalTheory.RayOnto
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

theorem exists_cmObj_extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ p q) (j : K →+* K') (σ' : K' →+* ℂ)
    (h : σ'.comp j = σ) :
    ∃ (X' : CMObj H K' (RingOfIntegers.mapRingHom j ρ) σ' p q)
      (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
      (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
      X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := by
  set f := RingOfIntegers.mapRingHom j with hf
  have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
  choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
  obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
  have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
  choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
  have hpt := spMap_int j h
  refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K' j X.split |>.1
            ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
            A := A', B := B'
            typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
            typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
            typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
            hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
  · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
    have e := congrArg Over.Hom.left ((X.lin i).2 c)
    simp only [Over.comp_left] at e
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
      (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
  · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
    choose pA hA using fun b => exists_ptEquiv (a b) hpt
    obtain ⟨x, hx⟩ := X.onto (pB y)
    refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
    rw [hx, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    apply Over.OverMorphism.ext
    simp only [Function.comp_apply]
    rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
    erw [hφ]
    rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
  · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
      (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
      ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
    rw [hpt]
    exact X.weil i

end Extend

section Conclusions

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe}

variable {Xo} {Z : CMLat hP D.p D.q} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
  {K' : Type} [Field K'] [NumberField K'] {κ : KA l →+* K'} {σ' : K' →+* ℂ} {k : IntermediateField ℚ ℂ}

end Conclusions

section ChangeOfExp

variable {D₁ D₂ : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)}

end ChangeOfExp

section Point

end Point

section Tensor

end Tensor

end GlobalTheory.CMExistsCompare
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  first | exact @GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | exact GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde | (intros; apply GlobalTheory.FinalJoin2.ReadTwist.exists_xiOK_xiTilde <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := GlobalTheory.T.field_size_adjoin_kth_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize


end GlobalTheory.FieldSize
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitary_reduction_polynomial_height_bound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → OrthoSmall D.host.E → DenomBound θ V → ∃ (d : ℕ) (C : ℝ) (M : ℕ), 0 < d ∧ ∀ g : GA D V, ∃ γ ∈ GQ V, BddDen V d (γ * g) ∧ normInf θ V γ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M := by
  first | exact @GlobalTheory.SmoothForms.Reduce.reduction | exact GlobalTheory.SmoothForms.Reduce.reduction | (intros; apply GlobalTheory.SmoothForms.Reduce.reduction <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.hasSum_compactUnitaryFourier_value_one : ∀ {n : ℕ} (ε : Fin n → Bool) (e : ℕ → KG ε → ℂ), (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ g : KG ε → ℂ, Continuous g → ∀ b : ℕ → ℝ, Summable b → (∀ i (k' : KG ε), ‖∫ k, e i k * g (k' * k) ∂(muK ε)‖ ≤ b i) → HasSum (fun i => ∫ k, e i k * g k ∂(muK ε)) (g 1) := by
  first | exact @GlobalTheory.KFourier.hasSum_kFourier | exact GlobalTheory.KFourier.hasSum_kFourier | (intros; apply GlobalTheory.KFourier.hasSum_kFourier <;> assumption)
end
