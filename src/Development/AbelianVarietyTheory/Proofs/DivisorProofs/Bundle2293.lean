module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle035
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.memIdealIntegral_tensorSwap_iff_mem_idealSubgroup : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.StdRead.IdealDict.inId_toE_iff | exact GlobalTheory.StdRead.IdealDict.inId_toE_iff | (intros; apply GlobalTheory.StdRead.IdealDict.inId_toE_iff <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.unitDetCharIndicator_eq_one_of_congruent_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  first | exact @GlobalTheory.StdRead.CongOneChar.unitChar_cong | exact GlobalTheory.StdRead.CongOneChar.unitChar_cong | (intros; apply GlobalTheory.StdRead.CongOneChar.unitChar_cong <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.exists_integral_unitary_lift_idempotentPart : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  first | exact @GlobalTheory.StdRead.IntLift.exists_lift | exact GlobalTheory.StdRead.IntLift.exists_lift | (intros; apply GlobalTheory.StdRead.IntLift.exists_lift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

theorem _root_.GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ, TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  first | exact @GlobalTheory.TwoTors.killsSq_of_triCocycle | exact GlobalTheory.TwoTors.killsSq_of_triCocycle | (intros; apply GlobalTheory.TwoTors.killsSq_of_triCocycle <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  first | exact @GlobalTheory.CompHS.ksRel_unique_ne_zero | exact GlobalTheory.CompHS.ksRel_unique_ne_zero | (intros; apply GlobalTheory.CompHS.ksRel_unique_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

open PureTriple

theorem exists_prod_act_comp_eq_one_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  intro E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdA := hA ℂ (RingHom.id ℂ) Function.injective_id
  have hdB := hB ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdA hdB
  simp only [RingHom.id_apply] at hdA hdB
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧
      (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧
      ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ b') := by
    intro T a b hd
    by_cases h0 : ρ = H.rt0
    · exact ⟨a, b, rfl, h0 ▸ hd⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hd τ).1 (h2 τ h)⟩⟩
  obtain ⟨pA, qA, hpqA, hdetA⟩ := key A 1 0 hdA
  obtain ⟨pB, qB, hpqB, hdetB⟩ := key B p q hdB
  obtain ⟨gA, tyA, htyA⟩ := AllClasses.exists_isTypeFn H pA qA
  obtain ⟨gB, tyB, htyB⟩ := AllClasses.exists_isTypeFn H pB qB
  obtain ⟨uA, HA, χA, -, hAH, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hBH, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩ := exists_datum_period hT hL A htyA hdetA uA hAH
  obtain ⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩ := exists_datum_period hT hL B htyB hdetB uB hBH
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH
  choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1
  let GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap
  let GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := fun s =>
    FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap
  have hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hactA s (FA.symm z)
    rw [FA.apply_symm_apply] at e
    exact e
  have hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s := fun s z => by
    have e := hactB s (FB.symm z)
    rw [FB.apply_symm_apply] at e
    exact e
  have hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a)) := fun s a => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPA.1 s a i).symm
  have hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b)) := fun s b => by
    simp only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    exact (hPB.1 s b i).symm
  have hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z) := fun r s z => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    ext i
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0 := fun r hr z hz => by
    have hr' : (r : E) ≠ 0 := by exact_mod_cast hr
    have e : diagMul tyB (r : E) (FB.symm z) = 0 := by
      have := congrArg FB.symm hz
      simpa [GB] using this
    have e' : FB.symm z = 0 := funext fun k => by
      have := congrFun e k
      simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left ((map_ne_zero (tyB k)).2 hr')
    simpa using congrArg FB e'
  have hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z) := by
    intro i s z
    haveI := (hψ i).isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i)
      (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have := DA.fin
  have := DA.proj
  have := DB.fin
  have := DB.proj
  have hrkA : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hpA, hqA, hpqA]
  haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : DA.La)
  have hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b) := fun i => by
    have hm : Ψ i (FA (PeA a)) ∈ uB.Λ := hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))
    exact ⟨b, by rw [hb, FB.apply_symm_apply]⟩
  choose b hb using hb
  have hrkB : Module.finrank (𝓞 E) DB.La = p + q := by rw [DB.rank, hpB, hqB, hpqB]
  have hni : ¬ LinearIndependent (𝓞 E) b := fun hi => by
    have := hi.fintype_card_le_finrank
    rw [Fintype.card_fin, hrkB] at this
    omega
  obtain ⟨x, hx, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hni
  refine ⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩
  let Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := ∑ i, Ψ i ∘ₗ GA (x i)
  have hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z) := fun z => by
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]
  have hΘa : Θ (FA (PeA a)) = 0 := by
    rw [hΘ]
    calc ∑ i, Ψ i (GA (x i) (FA (PeA a))) = ∑ i, FB (PeB (x i • b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcomm, hb, hGPB]
      _ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]
  have hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z) := fun s z => by

    rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGAc, hcomm]
  have hΘl : ∀ a', Θ (FA (PeA a')) = 0 := fun a' => by
    obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul hrkA ha a'
    refine hGBinj r hr _ ?_
    rw [← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]
  have hΘ0 : Θ.restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on uA.full fun z hz => ?_
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))
    have ez : z = FA (PeA a') := by rw [ha', FA.apply_symm_apply]
    rw [ez]
    exact hΘl a'
  have hΘz : ∀ z, Θ z = 0 := fun z => LinearMap.congr_fun hΘ0 z
  have hs : Smooth A.t.G.hom := A.ab.smooth
  have hp : IsProper B.t.G.hom := B.ab.proper
  have hr : IsReduced A.t.G.left := isReduced_of_smooth_complex _ A.t.G.hom hs
  refine ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_
  obtain ⟨z, rfl⟩ := uA.ex_onto y
  have hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) =
      uB.ex (∑ i ∈ s, Ψ i (GA (x i) z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]; exact ((uB.ker 0).2 uB.Λ.zero_mem).symm
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]
  rw [hpr, ← hΘ, hΘz, comp_one]
  exact (uB.ker 0).2 uB.Λ.zero_mem

end GlobalTheory.CM.PureHom
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem valR_spMap_comp {Z : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S')
    (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valR (spMap σ ≫ z) U f = σ (valR z U f) := by
  have h' := GlobalTheory.FlagMod.le_preimage_comp (spMap σ) h
  rw [valR_eq_ev _ _ h', valR_eq_ev _ _ h, GlobalTheory.FlagMod.ev_spMap σ z U h h']
  rfl

theorem top_le_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (transl φ x v) ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← (isTransl_transl φ x hx v).red hv] at this
  exact this

theorem transl_spMap {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B B' : Type} [CommRing B] [CommRing B']
    (φ : K →+* B) (σ : B →+* B') (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) :
    transl (σ.comp φ) (spMap σ ≫ x) v = spMap (dualMap σ) ≫ transl φ x v := by
  have hx' : (spMap σ ≫ x) ≫ A.hom = spMap (σ.comp φ) := by
    rw [Category.assoc, hx, Cris.spMap_comp]
  exact (isTransl_transl _ _ hx' v).unique ((isTransl_transl φ x hx v).map σ)

theorem baseMap_eq {K : Type} [Field K] {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B']
    [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B') :
    baseMap K B' = (ρ : B →+* B').comp (baseMap K B) :=
  RingHom.ext fun k ↦ by simp [baseMap]

theorem dualMap_snd {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (c : DualNumber B) :
    (dualMap σ c).snd = σ c.snd := by
  simp [dualMap]

section Map

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
  {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B'] [Algebra (DualNumber K) B']

theorem dlogAt_spMap (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) {v : epsR K ⟶ A} (hv : IsTangent v) {Wo : A.left.Opens}
    (g : Γ(A.left, Wo)ˣ) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) :
    dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) v Wo g = ρ (dlogAt (baseMap K B) x v Wo g) := by
  rw [dlogAt, dlogAt, baseMap_eq ρ, transl_spMap _ _ x hx v,
    valR_spMap_comp _ _ _ (top_le_transl _ x hx hv hxWo), valR_spMap_comp _ _ _ hxWo, dualMap_snd, map_mul]
  rfl

theorem chartVal_spMap {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo)
    (hut : ∀ a, IsTangent (u a)) (f : Γ(Z, Ω)) :
    chartVal m Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) f = ρ (chartVal m Ω δ u θ Wo g x f) := by
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω := hxΩ
  have ht : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω := fun a ↦
    top_le_transl _ x hx (hut a) hxΩ
  have hd : ∀ b, dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u b) Wo g =
      ρ (dlogAt (baseMap K B) x (u b) Wo g) := fun b ↦ dlogAt_spMap ρ hx (hut b) g hxWo
  have htr : ∀ a, transl (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u a) =
      spMap (dualMap (ρ : B →+* B')) ≫ transl (baseMap K B) x (u a) := fun a ↦ by
    rw [baseMap_eq ρ]; exact transl_spMap _ _ x hx (u a)
  simp only [chartVal, hd, htr, Category.assoc]

  simp only [valR_spMap_comp _ _ _ hxm, valR_spMap_comp _ _ _ (ht _), dualMap_snd, map_add (f := _), map_mul, map_sum]
  simp only [RingHom.coe_coe, AlgHom.commutes, baseMap_eq ρ, RingHom.comp_apply]

end Map

theorem isChartPt_spMap : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  intro K _ A _ A' Z m m' Ω δ n u θ Wo g B _ _ x l hx hxΩ hxWo hut hl B' _ _ ρ
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [Category.assoc, h1, ← Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [Category.assoc]
    exact GlobalTheory.FlagMod.le_preimage_comp _ h2
  · rw [Category.assoc, valR_spMap_comp _ _ _ h2, h3 f, chartVal_spMap m Ω δ u θ Wo g ρ hx hxΩ hxWo hut f]
    rfl

end GlobalTheory.CechKS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin


set_option backward.isDefEq.respectTransparency false in
theorem stalkClosedPointTo_localMap_comp {X : Scheme.{0}} {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B]
    (x : Spec A ⟶ X) (g : A ⟶ B) [IsLocalHom g.hom] (y : Spec B ⟶ X) (hy : y = Spec.map g ≫ x) (x₀ : X)
    (h₁ : x (IsLocalRing.closedPoint A) = x₀) (h₂ : y (IsLocalRing.closedPoint B) = x₀) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo y =
      ((X.presheaf.stalkCongr (Inseparable.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo x) ≫ g := by
  subst h₁
  have hy' : y = Spec.map (Scheme.stalkClosedPointTo x ≫ g) ≫ X.fromSpecStalk _ := by
    rw [hy, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  clear hy
  subst hy'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo x ≫ g).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo x ≫ g) U _

theorem tanDer_smul : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  intro R _ _ G _ _ r v f
  have hl : IsLocalHom (CommRingCat.ofHom (epsMul r)).hom := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hy : (tv (r • v)).left = Spec.map (CommRingCat.ofHom (epsMul r)) ≫ (tv v).left := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left]
  have key := stalkClosedPointTo_localMap_comp (A := CommRingCat.of (DualNumber R)) (B := CommRingCat.of (DualNumber R))
    (tv v).left (CommRingCat.ofHom (epsMul r)) (tv (r • v)).left hy (origin G) (tv_closedPoint G v)
    (tv_closedPoint G (r • v))
  rw [tanDer_eq, tanDer_eq]
  refine (congrArg (fun φ => (φ.hom f).snd) key).trans ?_
  have hs : ∀ a : DualNumber R, (epsMul r a).snd = r * a.snd := fun a => by simp [epsMul]
  exact hs _

end GlobalTheory.CoordsOrigin
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R), evO G (constO G r) = r := by
  first | exact @GlobalTheory.FormalOrigin.evO_constO | exact GlobalTheory.FormalOrigin.evO_constO | (intros; apply GlobalTheory.FormalOrigin.evO_constO <;> assumption)
end
