module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqTan
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

attribute [local instance] Over.cartesianMonoidalCategory

namespace ExpBijectiveUniformisation

section Help

variable {X Y Z : Scheme.{0}}

lemma wchart_comp_le (L : LB X) (g : Y ⟶ X) (z : Z ⟶ Y) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0) ≤ z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => g) j := by
  intro y hy
  have h1 : (z ≫ g).base y ∈ L.U (j 0) := Set.mem_iInter.1 hy ⟨⟩
  show z.base y ∈ (⋂ k : Fin 1, g.base ⁻¹' (L.U (j k) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact h1

def genCast {L L' : LB X} (h : L = L') {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L' φ ε) :=
  h ▸ b

def sumQ {X1 Xn : Type} [AddCommGroup X1] [AddCommGroup Xn] {n : ℕ} (xe : Xn ≃+ (Fin n → X1)) (Q : X1 → ℤ) :
    Xn → ℤ :=
  fun x => ∑ i, Q (xe x i)

end Help

section GermN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def jcN (V F : Type) [CommRing V] [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    Sp (Jet F (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap (((jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) :
      Jet F (Fin 1 × Fin d) m →+* Jet F (Fin n × Fin d) m).comp
    (jetCoef (algebraMap V F) (Fin 1 × Fin d) m))

def jptN {V : Type} [CommRing V] {t : SAB H (Sp V)} {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (F : Type)
    [Field F] [Algebra V F] (n m : ℕ) (i : Fin n) : Sp (Jet F (Fin n × Fin d) m) ⟶ t.G.left :=
  jcN V F d n m i ≫ (xT m).left

def IsGermN {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d n : ℕ}
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' t.G n)
    {U' : Unif I D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ)
    (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d) : Prop :=
  ∀ m, ∃ (z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left)
    (τ : LB.Gen (LB.LinComb U'.LG.L (K := PUnit.{1}) (fun _ => z ≫ UnifPre.gFK (R := V) (G := G') F)
      (fun _ => (q : ℤ))))
    (b : LB.Gen (LB.LinComb P.U.LG.L (K := Fin n)
      (fun i => (z ≫ UnifPre.gFK (R := V) (G := G') F) ≫ (pG.pr i).left) (fun _ => (q : ℤ)))),
    z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
    (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
    GeneratorPullback.MapsAt P.U.LG.L U'.LG.L (fun i => (pG.pr i).left) PU.wL (z ≫ UnifPre.gFK (R := V) (G := G') F) q τ b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (genCast (congrArg RigLB.L P.bundle) _ _ b)
      (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)) ∧
    ∀ j : Fin 1 → U'.LG.L.ι,
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map
          (homOfLE (wchart_comp_le U'.LG.L (UnifPre.gFK (R := V) (G := G') F) z j)).op).hom
        ((z.app _).hom (σ'.f j)) =
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map (homOfLE le_top).op).hom (toΓ _ (psJet m f)) *
        (τ.s (fun _ => j 0)).val

end GermN

section St

open IsLocalRing

end St

end ExpBijectiveUniformisation

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem jetMap_mk {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') (p : MvPolynomial ι R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl

theorem jetTrunc_mk (p : MvPolynomial ι R) :
    (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem jet_hom_ext {B : Type} [CommRing B] [Algebra R B] {f g : Jet R ι m →ₐ[R] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)

private theorem deg_sum_lemma {κ : Type} (e : κ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree]
  | exact Finsupp.degree_apply e

theorem monomial_mem_orig_pow (e : ι →₀ ℕ) (c : R) : monomial e c ∈ orig R ι ^ e.degree := by
  classical
  rw [MvPolynomial.monomial_eq, Finsupp.prod]
  refine Ideal.mul_mem_left _ _ ?_
  rw [deg_sum_lemma e, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (X_mem_orig i) _

theorem mem_orig_pow_of {n : ℕ} {p : MvPolynomial ι R} (h : ∀ e ∈ p.support, n ≤ e.degree) :
    p ∈ orig R ι ^ n := by
  rw [p.as_sum]
  exact Ideal.sum_mem _ fun e he => Ideal.pow_le_pow_right (h e he) (monomial_mem_orig_pow e _)

private theorem mem_degLE_lemma [Fintype ι] [DecidableEq ι] (k : ℕ) (e : ι →₀ ℕ) :
    e ∈ degLE k ↔ e.degree ≤ k := by
  unfold degLE
  rw [Finset.mem_filter, deg_sum_lemma]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, h⟩
    · have hle : e i ≤ ∑ j ∈ e.support, e j := by
        by_cases hi : i ∈ e.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · have h0 : e i = 0 := by simpa [Finsupp.mem_support_iff] using hi
          rw [h0]
          exact Nat.zero_le _
      omega
    · ext i
      simp

private theorem coeff_psTrunc_lemma_2 [Fintype ι] [DecidableEq ι] (k : ℕ) (g : MvPowerSeries ι R)
    (e : ι →₀ ℕ) :
    AddMonoidAlgebra.coeff (psTrunc k g) e = if e.degree ≤ k then MvPowerSeries.coeff e g else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : e.degree ≤ k
  · rw [if_pos ((mem_degLE_lemma k e).2 h), if_pos h]
  · rw [if_neg (mt (mem_degLE_lemma k e).1 h), if_neg h]

theorem psTrunc_succ_sub [Fintype ι] [DecidableEq ι] (g : MvPowerSeries ι R) :
    psTrunc (m + 1) g - psTrunc m g ∈ orig R ι ^ (m + 1) := by
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ m := by omega
  rw [if_pos h1, if_pos (by omega : e.degree ≤ m + 1), sub_self] at he
  exact he rfl

theorem exists_ps_of_jets [Fintype ι] [DecidableEq ι] (a : ∀ m, Jet R ι m)
    (ha : ∀ m, (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) (a (m + 1)) = a m) :
    ∃ f : MvPowerSeries ι R, ∀ m, psJet m f = a m := by
  choose p hp using fun k => Ideal.Quotient.mk_surjective (a k)
  have hc : ∀ k l, k ≤ l → p l - p k ∈ orig R ι ^ (k + 1) := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ l hkl ih =>
      have h1 : p (l + 1) - p l ∈ orig R ι ^ (l + 1) := by
        rw [← Ideal.Quotient.eq]
        have h := ha l
        rw [← hp (l + 1), ← hp l, jetTrunc_mk] at h
        exact h
      have h2 : orig R ι ^ (l + 1) ≤ orig R ι ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ (h2 h1) ih
      rwa [sub_add_sub_cancel] at h3
  obtain ⟨f, hf⟩ : ∃ f : MvPowerSeries ι R, ∀ e, MvPowerSeries.coeff e f = AddMonoidAlgebra.coeff (p e.degree) e :=
    ⟨fun e => AddMonoidAlgebra.coeff (p e.degree) e, fun e => rfl⟩
  refine ⟨f, fun k => ?_⟩
  rw [← hp k]
  unfold psJet
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_of
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_psTrunc_lemma_2] at he
  by_contra hlt
  have h1 : e.degree ≤ k := by omega
  rw [if_pos h1] at he
  apply he
  have h3 := coeff_eq_zero_of_mem (hc e.degree k h1) (by omega : e.degree < e.degree + 1)
  rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
  rw [hf, sub_eq_zero]
  exact h3.symm

end Alg

section Subst

variable {R : Type} [CommRing R] {d : ℕ}

abbrev sL (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    Jet R (Fin 2 × Fin d) m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (g j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) R) p.1 p.2

theorem power_series_in_fin_one (m : ℕ) (g : MvPowerSeries (Fin 1 × Fin d) R) : psIn d m ![0] g = psTrunc m g := by
  unfold psIn
  have h : (fun p : Fin 1 × Fin d => ((![0] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h]
  simp

theorem sL_copy0 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id R _ := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk]

theorem sL_copy1 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  apply jet_hom_ext
  rintro ⟨i1, j⟩
  obtain rfl : i1 = 0 := Subsingleton.elim _ _
  simp [sL, jetSubstP, jetCopy, jetMap_mk, power_series_in_fin_one]

private theorem const_psTrunc_lemma_3 {κ : Type} [Fintype κ] [DecidableEq κ] (k : ℕ) (g : MvPowerSeries κ R) :
    MvPolynomial.constantCoeff (psTrunc k g) = MvPowerSeries.coeff 0 g := by
  rw [show MvPolynomial.constantCoeff (psTrunc k g) = AddMonoidAlgebra.coeff (psTrunc k g) 0 from rfl,
    coeff_psTrunc_lemma_2, if_pos (by simp)]

theorem sL_trunc (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) R) :
    (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _).comp (sL (m + 1) g) =
      (sL m g).comp (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, jetTrunc_mk, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  rw [Ideal.Quotient.eq]
  fin_cases k
  · simp
  · simp only [power_series_in_fin_one, Matrix.cons_val_one, Matrix.head_cons]
    change psTrunc (m + 1) (g j) - C (MvPolynomial.constantCoeff (psTrunc (m + 1) (g j))) -
      (psTrunc m (g j) - C (MvPolynomial.constantCoeff (psTrunc m (g j)))) ∈ _
    rw [const_psTrunc_lemma_3, const_psTrunc_lemma_3, sub_sub_sub_cancel_right]
    exact psTrunc_succ_sub (g j)

theorem copy_trunc (m : ℕ) (i : Fin 2) :
    (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _) := by
  apply jet_hom_ext
  intro p
  simp [jetCopy, jetMap_mk, jetTrunc_mk]

end Subst

section Over

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap, ← Spec.map_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap]

end Over

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Bridge

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

abbrev GS : Over (Spec (CommRingCat.of S)) := (Over.pullback x0).obj G

instance : GrpObj (GS G x0) := Functor.grpObjObj

def br {A : Type} [CommRing A] [Algebra S A] (f : overAt x0 A ⟶ G) : sp (R₀ := S) A ⟶ GS G x0 :=
  (Over.mapPullbackAdj x0).homEquiv (sp (R₀ := S) A) G f

variable {G x0}

theorem br_injective {A : Type} [CommRing A] [Algebra S A] : Function.Injective (br G x0 (A := A)) := by
  intro f g h
  exact ((Over.mapPullbackAdj x0).homEquiv _ _).injective h

theorem br_mul {A : Type} [CommRing A] [Algebra S A] (f g : overAt x0 A ⟶ G) :
    br G x0 (f * g) = br G x0 f * br G x0 g := by
  simp only [br, Adjunction.homEquiv_unit]
  first
  | rw [Functor.map_mul, comp_mul]
  | rw [Functor.map_mul, Hom.comp_mul]
  | rw [Functor.map_mul, MonObj.comp_mul]
  | rw [Functor.map_mul, Mon_Class.comp_mul]

theorem br_one {A : Type} [CommRing A] [Algebra S A] : br G x0 (1 : overAt x0 A ⟶ G) = 1 := by
  simp [br, Adjunction.homEquiv_unit]

theorem homAt_eq {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (ψ : A →ₐ[S] B) :
    homAt x0 ψ = (Over.map x0).map (spMap ψ) := by
  first
  | rfl
  | exact Over.OverMorphism.ext rfl

theorem br_comp {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (ψ : A →ₐ[S] B)
    (f : overAt x0 A ⟶ G) : br G x0 (homAt x0 ψ ≫ f) = spMap ψ ≫ br G x0 f := by
  unfold br
  rw [homAt_eq, Adjunction.homEquiv_naturality_left]

end Bridge

theorem expUniqLoc : ExpUniqLocSt := by
  intro E _ _ _ H Dw l Xo S _ _ _ x0 d x x' hx hx' ht
  haveI : IsCommMonObj Xo.univ.t.G := Xo.univ.t.semi.comm
  haveI : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  haveI : Smooth (GS Xo.univ.t.G x0).hom := by
    show Smooth (pullback.snd Xo.univ.t.G.hom x0)
    infer_instance
  obtain ⟨n, xu, hxu⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc (GS Xo.univ.t.G x0)
  have key : ∀ m, br Xo.univ.t.G x0 (x' m * (x m)⁻¹) = 1 := by
    refine trivT hxu (fun m => br Xo.univ.t.G x0 (x' m * (x m)⁻¹)) ?_ ?_ ?_
    · intro m
      rw [← br_comp]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, hx.1 m, hx'.1 m]
    · intro m
      rw [← br_comp, ← br_comp, ← br_comp, ← br_mul]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv]
      rw [hx.2 m, hx'.2 m, _root_.mul_inv, _root_.mul_mul_mul_comm]
    · intro j
      rw [← br_comp, ← br_one (A := DualNumber S)]
      congr 1
      simp only [MonObj.comp_mul, GrpObj.comp_inv, ht j, _root_.mul_inv_cancel]
  funext m
  have h := key m
  rw [← br_one] at h
  exact (_root_.mul_inv_eq_one.1 (br_injective h)).symm

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqBC
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S]

def actPS (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) • MvPowerSeries.X q

def φa (c : Coeff l) [Algebra c.F S] {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (a : 𝓞 E) :
    Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun j => MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)

def atP {d n : ℕ} (P : Fin n → Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (f : MvPowerSeries (Fin n × Fin d) S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin n × Fin d => P p.1 p.2) f

end Defs

def UnitIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
      (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
      ∀ a : 𝓞 E,
        Germ.FB.expS S (-(compL (φa c φ (1 + a * H.bar a)) (C.B.hL S C.h H.w0))) *
            atP ![φa c φ a, φa c φ H.w0] (C.B.ad (H.bar a)) =
          atP ![φ, φa c φ (a * H.bar a), φa c φ ((1 + a * H.bar a) * H.w0)] C.B.ph1 *
            atP ![φ, φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φa c φ (a * H.bar a), φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φ, φa c φ (a * H.w0)] (C.B.ad a) *
            Germ.FB.expS S (-(compL (φa c φ a) (C.B.hL S C.h H.w0))) ^ 2 *
            Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))) *
            Germ.FB.expS S (-(compL (φa c φ (a * H.bar a)) (C.B.hL S C.h H.w0)))

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
end
end
