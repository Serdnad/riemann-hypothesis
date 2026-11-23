module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointDesc

theorem hasGen_of_comp {X Y Z : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (h : Z ⟶ Y) (m : Z ⟶ X)
    (hm : h ≫ f = m) (H : HasGen (L.pull f)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := H
  subst hm
  exact ⟨LB.pullGen L (fun _ : PUnit => f) (fun _ => 1) t h,
    DVR.pullGen_isGen L (fun _ : PUnit => f) (fun _ => 1) t ht h⟩

theorem hasGen_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y)
    (H : HasGen (L.pull (h ≫ f))) : HasGen ((L.pull f).pull h) := by
  obtain ⟨t, ht⟩ := H
  exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB (pull_isLB hL f) h)
    (GlobalTheory.FamRep.lbIso_pull_pull hL f h).symm t ht

theorem hasGen_lam_pull_of_eq_on_open : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  intro A _ hA M hM T x U y t ht hU H
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _

  let x0 : U.toScheme := ⟨t, ht⟩
  let K : Type := U.toScheme.residueField x0
  letI : Field K := inferInstanceAs (Field (U.toScheme.residueField x0))
  let q : Sp K ⟶ U.toScheme := U.toScheme.fromSpecResidueField x0
  let p : Sp K ⟶ T.left := q ≫ U.ι
  let φ := Spec.preimage (p ≫ T.hom)
  let β : ℂ →+* K := φ.hom
  have hβ : spMap β = p ≫ T.hom := Spec.map_preimage _
  let Tk : Over (Sp ℂ) := Over.mk (spMap β)
  let pk : Tk ⟶ T := Over.homMk p hβ.symm
  have hxy : pk ≫ x = toUnit Tk ≫ y := by
    ext1
    simp only [Over.comp_left, Over.homMk_left, pk, Over.toUnit_left]
    show (q ≫ U.ι) ≫ x.left = Tk.hom ≫ y.left
    simp only [Tk, Over.mk_hom, hβ, p, Category.assoc, hU]
  let e : A ⟶ A ⊗ 𝟙_ (Over (Sp ℂ)) := lift (𝟙 A) (toUnit A)
  let g := lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)
  have sq : (A ◁ pk) ≫ lift (fst A T) (snd A T ≫ x) = fst A Tk ≫ e ≫ g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e, g]
    · simp only [Category.assoc, lift_snd, e, g, lift_fst_assoc, lift_snd_assoc]
      rw [whiskerLeft_snd_assoc, hxy, ← Category.assoc, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  have H₁ : HasGen ((abelian₂ A M).pull ((fst A Tk).left ≫ (e ≫ g).left)) :=
    hasGen_of_comp _ (A ◁ pk).left _ (by rw [← Over.comp_left, sq, Over.comp_left]) H
  have H₂ := hasGen_pull_pull hL (e ≫ g).left (fst A Tk).left H₁
  have hpb : IsPullback (fst A Tk).left (snd A Tk).left A.hom (spMap β) := IsPullback.of_hasPullback _ _
  obtain ⟨u, hu⟩ := GlobalTheory.FieldTriv.exists_gen_of_field_extension ℂ K β A hA _ (fst A Tk).left (snd A Tk).left hpb
    ((abelian₂ A M).pull (e ≫ g).left) (pull_isLB hL _) H₂
  refine hasGen_of_comp (e ≫ g).left (fst A (𝟙_ (Over (Sp ℂ)))).left _ ?_ ⟨u, hu⟩
  rw [← Over.comp_left]
  congr 1
  rw [← Category.assoc]
  have : fst A (𝟙_ (Over (Sp ℂ))) ≫ e = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, lift_snd, Category.id_comp]
      exact toUnit_unique _ _
  rw [this, Category.id_comp]

end GlobalTheory.PointDesc
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.isLogCanonicalEquation_changeForm_perturbed_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  first | exact @GlobalTheory.PairStep.isLogEqn_changeForm_add | exact GlobalTheory.PairStep.isLogEqn_changeForm_add | (intros; apply GlobalTheory.PairStep.isLogEqn_changeForm_add <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Published

theorem arProj_of_heightProjection (H : HeightProjection) : ArProj := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hm
  have key (L : HermLB p) (a : ℝ) (ha : L.IsSelfInter a) :
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a) := by
    obtain ⟨h, hh, rfl⟩ := ha
    have := H k X Y p q D D hX hY π hπ (by
      rw [hg, (genericPoint_spec X).def]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq) hm L h hh
    exact (congrArg (fun x => (π.residueDegree (genericPoint Y) : ℝ) * h x) hg) ▸ this
  refine ⟨key, fun ι _ L Φ hΦ => ⟨fun n => ?_, fun P d hd hP => ?_⟩⟩
  · exact (ArInt.isometric_comb_pull L n π hπ).symm.isSelfInter hY (key _ _ (hΦ.1 n))
  · rw [LinearMap.smul_apply, hΦ.2 P d hd hP, smul_zero]

end GlobalTheory.Published
end

section

open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a), g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  first | exact @GlobalTheory.CentralExponent.abs_le_of_conj_mem | exact GlobalTheory.CentralExponent.abs_le_of_conj_mem | (intros; apply GlobalTheory.CentralExponent.abs_le_of_conj_mem <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSubgroup

theorem exists_finite_subgroup_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro K _ _ A _ hA
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  obtain ⟨H₀, m, s, hH₀, hva, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K A hA
  have hP : IsProjBy A.hom := ⟨H₀, hH₀, m, s, hva⟩
  obtain ⟨L, hL, hR⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy hP
  obtain ⟨H, j, hj, hf, hH⟩ := GlobalTheory.KernelRep.exists_finite_closed_kernel hG K A hA L hL hR
  haveI : Mono j.left := inferInstance
  haveI : Mono j := (Over.forget _).mono_of_mono_map this
  have hjK : GlobalTheory.MemKL A L j := (hH H j).2 ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (hH _ (1 : 𝟙_ (Over (Sp K)) ⟶ A)).1 (GlobalTheory.memKL_one hL _)
  have hm := (hH _ ((fst H H ≫ j) * (snd H H ≫ j))).1
    (GlobalTheory.UU.InK.mul hL (hjK.comp (fst H H)) (hjK.comp (snd H H)))
  have hn := (hH _ j⁻¹).1 (GlobalTheory.UU.InK.inv hL hjK)
  obtain ⟨g, hg⟩ := GlobalTheory.PointQuot.exists_grpObj_of_mono j h1.choose hm.choose hn.choose
    h1.choose_spec hm.choose_spec hn.choose_spec
  exact ⟨L, H, g, j, hL, hP, GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA L hL, hg, hj, hf, hH⟩

end GlobalTheory.KernelSubgroup
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.additive_strongApproximation_avoiding_finset : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  first | exact @GlobalTheory.AddApproxPlaces.exists_approx_notMem | exact GlobalTheory.AddApproxPlaces.exists_approx_notMem | (intros; apply GlobalTheory.AddApproxPlaces.exists_approx_notMem <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open Filter Topology

namespace GlobalTheory.SUTrunc

section Mat

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e : R}

theorem idempotentTruncation_preserves_form (he : e * e = e) {A B J : Matrix n n R} (h : A * J * B = J) :
    (1 + e • (A - 1)) * J * (1 + e • (B - 1)) = J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, he, h]
  abel

theorem trunc_mul (he : e * e = e) {A B : Matrix n n R} (h : A * B = 1) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 := by
  have := idempotentTruncation_preserves_form he (A := A) (B := B) (J := 1) (by rw [Matrix.mul_one, h])
  rwa [Matrix.mul_one] at this

theorem cT_trunc (c : R →+* R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem det_trunc (he : e * e = e) {A : Matrix n n R} (h : A.det = 1) : (1 + e • (A - 1)).det = 1 := by
  have key : ∀ (a : R) (B : Matrix n n R), B.det = 1 → (∀ i j, a ∣ (1 + e • (A - 1)) i j - B i j) →
      a ∣ (1 + e • (A - 1)).det - 1 := by
    intro a B hB hd
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, ← hB, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hd i j
  obtain ⟨x, hx⟩ := key e 1 Matrix.det_one fun i j => ⟨(A - 1) i j, by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring⟩
  obtain ⟨y, hy⟩ := key (1 - e) A h fun i j => ⟨-((A - 1) i j), by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]; ring⟩
  linear_combination (1 - e) * hx + e * hy + (-x - y) * he

end Mat

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (h : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, mul_one]
    · rw [h2 w hw, mul_zero]
  · change evalV F v (sndA F η) * evalV F v (sndA F η) = evalV F v (sndA F η)
    by_cases hw : v ∈ S₂
    · rw [h3 v hw, mul_one]
    · rw [h4 v hw, mul_zero]

theorem tendsto_idem (η : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hη : ∀ T, IsPlacesIdem Finset.univ T (η T)) : Tendsto η atTop (𝓝 1) := by
  classical
  let y : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun T v => if v ∈ T then 1 else 0
  have hy : Tendsto y atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    exact (if_pos (hT (Finset.mem_singleton_self v))).symm
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : Continuous fun z => pairA F 1 (s z) := continuous_const.prodMk hs
  have h1 : pairA F 1 (s 1) = 1 := rfl
  have h2 : η = fun T => pairA F 1 (s (y T)) := by
    funext T
    obtain ⟨h1, -, h3, h4⟩ := hη T
    refine Prod.ext (funext fun w => h1 w (Finset.mem_univ w)) (RestrictedProduct.ext _ _ fun v => ?_)
    change evalV F v (sndA F (η T)) = ((y T v : v.adicCompletionIntegers F) : v.adicCompletion F)
    by_cases hv : v ∈ T
    · rw [h3 v hv]; simp [y, hv]
    · rw [h4 v hv]; simp [y, hv]
  rw [h2, ← h1]
  exact (hp.tendsto 1).comp hy

theorem mem_closure_supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  intro F E _ _ _ _ _ σ _ M J _ g hg
  choose η hη using fun T : Finset (HeightOneSpectrum (𝓞 F)) => StrongApprox.exists_isPlacesIdem Finset.univ T
  have hlim := tendsto_idem η hη
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have he : ∀ T, ι (η T) * ι (η T) = ι (η T) := fun T => by rw [← map_mul, idem_mul_self (hη T)]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin M) (AF F ⊗[F] E) := fun T =>
    ⟨1 + ι (η T) • (SUSuppSub.mv σ J g - 1), 1 + ι (η T) • (SUSuppSub.mv σ J g⁻¹ - 1),
      trunc_mul (he T) (SUSuppSub.mv_mul_inv σ J g), trunc_mul (he T) (SUSuppSub.mv_inv_mul σ J g)⟩
  have hu : ∀ T, u T ∈ HR (AF F) σ J := by
    intro T
    change Formalism.UG.cT (sigR (AF F) σ) (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) * JR (AF F) J *
      (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) = JR (AF F) J
    rw [cT_trunc _ (StrongApprox.sigR_algebraMap σ _)]
    exact idempotentTruncation_preserves_form (he T) (g : HR (AF F) σ J).2
  let x : Finset (HeightOneSpectrum (𝓞 F)) → HA (AF F) σ J := fun T => (⟨u T, hu T⟩ : HR (AF F) σ J)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hmat : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Tendsto (fun T => 1 + ι (η T) • (A - 1)) atTop (𝓝 A) := by
    intro A
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (hlim.smul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    rw [one_smul, Matrix.sub_apply, add_sub_cancel] at h
    refine h.congr fun T => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def]
  have hx : Tendsto x atTop (𝓝 g) := by
    refine (tendsto_subtype_rng (p := fun a => a ∈ HR (AF F) σ J)).2 ?_
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    exact (hmat (SUSuppSub.mv σ J g)).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (hmat (SUSuppSub.mv σ J g⁻¹)))
  refine mem_closure_of_tendsto hx (Eventually.of_forall fun T => ⟨Finset.univ, T, η T, hη T, ?_⟩)
  rw [SUSuppSub.mem_SUSupp_iff]
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_trunc (he T) (StrongApprox.mem_SUAdelic.1 hg)), ?_⟩
  change ι (η T) • (1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1) = 1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1
  rw [add_sub_cancel_left, smul_smul, he]

end GlobalTheory.SUTrunc

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_norm_solution_adelic_from_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E, (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.normEq_inf_place | exact GlobalTheory.normEq_inf_place | (intros; apply GlobalTheory.normEq_inf_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)) (hX : IsCompact X) (hcl : IsClosed (SUSupp σ J ε)) (hent : ∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) : IsCompact (SUSupp σ J ε) := by
  have hinv : ∀ g ∈ SUSupp σ J ε, g⁻¹ ∈ SUSupp σ J ε := by
    intro g hg
    rw [GlobalTheory.SUSuppSub.mem_SUSupp_iff] at hg ⊢
    exact ⟨(SUAdelic σ J).inv_mem hg.1, GlobalTheory.SUSuppSub.fix_inv _ (GlobalTheory.SUSuppSub.mv_inv_mul σ J g) hg.2⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let S : Set (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => X
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hX
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  have hL := (GlobalTheory.AdelicU.isClosedEmbedding_matHom_GAd σ J).isCompact_preimage hK
  refine hL.of_isClosed_subset hcl fun g hg => ?_
  refine ⟨fun i _ j _ => hent g hg i j, ((HA.mat (AF F) σ J g⁻¹).1), fun i _ j _ => hent g⁻¹ (hinv g hg) i j, ?_⟩
  rfl
end GlobalTheory.SUSuppCompact

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E, (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.NormFin.idem_norm_eq_of_local | exact GlobalTheory.NormFin.idem_norm_eq_of_local | (intros; apply GlobalTheory.NormFin.idem_norm_eq_of_local <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isClosed_specialUnitarySupportedAtPlaces : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F), IsClosed (SUSupp σ J ε) := by
  first | exact @GlobalTheory.SUSuppClosed.isClosed_SUSupp | exact GlobalTheory.SUSuppClosed.isClosed_SUSupp | (intros; apply GlobalTheory.SUSuppClosed.isClosed_SUSupp <;> assumption)
end
