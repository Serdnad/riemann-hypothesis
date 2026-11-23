module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqOf_of_dim (hL : Out.Laws) (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R]
    [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c₀ : SiegPre h k ζ (spMap β))
    (hd : SmoothOfRelativeDimension h c₀.A.hom) (hc₀ : c₀.Principal) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c₀.A.left),
      (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧
        SqOf P c₀ (spMap (algebraMap R R₁)) φ := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have := (IsUnit.mk0 ((2 : ℕ) : ℚ) (by norm_num)).map (algebraMap ℚ R)
    rwa [map_natCast] at this
  obtain ⟨R', _, _, ⟨f₁, e₁, l₁⟩, H₁⟩ := GlobalTheory.T.exists_finiteEtale_cover_constant_torsion R c₀.A h 2 c₀.ab hd h2
  obtain ⟨c', m', hc'⟩ := pull_sieg (spMap ((algebraMap R R').comp β)) (spMap (algebraMap R R'))
    (SiegelRingChange.spMap_comp' _ _).symm c₀ hc₀
  have m'' := m'
  obtain ⟨φ', -, g', -⟩ := m''
  obtain ⟨i₀, hi₀⟩ := H₁ c'.A φ' g'
  letI : Algebra ℚ R' := ((algebraMap R R').comp (algebraMap ℚ R)).toAlgebra
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  obtain ⟨R₁, _, _, ⟨f₂, e₂, l₂⟩, H₂⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R' _ c' h i₀ hc'
  obtain ⟨c₁, m₁, hc₁⟩ := pull_sieg (spMap ((algebraMap R' R₁).comp ((algebraMap R R').comp β)))
    (spMap (algebraMap R' R₁)) (SiegelRingChange.spMap_comp' _ _).symm c' hc'
  have m₁' := m₁
  obtain ⟨φ₁, φ₂, g₁, sq₁, w₁, -⟩ := m₁'
  obtain ⟨i, hi, li⟩ := exists_pull_labels g₁ 2 i₀ hi₀
  letI : Algebra ℚ R₁ := ((algebraMap R' R₁).comp (algebraMap ℚ R')).toAlgebra
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R' R₁
  obtain ⟨u, j, huj⟩ := H₂ c₁.A φ₁ i _ g₁ hi rfl
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ c₁.A 2 c₁.ab (isUnit_two_sections R₁)
  have hψ : ∀ {T : Over (Sp R₁)} (x : T ⟶ c₁.A), x ≫ ((𝟙 c₁.A) ^ 2 : c₁.A ⟶ c₁.A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  have two : ∀ a : Multiplicative (Fin (2 * h) → ZMod 2), a ^ 2 = 1 := fun a => by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd a x) = y
    revert y; decide
  have hD : (c'.diag.pull φ₁).IsLB := pull_isLB (diag_isLB c') _
  obtain ⟨M, hM, iM, sM⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle _ c₁.A c₁.A ((𝟙 c₁.A) ^ 2) _ i (lbPow (c'.diag.pull φ₁) 2)
    (GlobalTheory.isLB_lbPow hD 2) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, ← map_pow, two, map_one])
    (fun K _ _ t => ⟨fun x => by rw [hψ]; exact (li K t).1 x, (li K t).2⟩) u j huj
  have iM' := (GlobalTheory.lbIso_lbPow (diag_iso sq₁ w₁) 2).trans (GlobalTheory.isLB_lbPow (diag_isLB c₁) 2) (GlobalTheory.isLB_lbPow hD 2)
    (pull_isLB hM _) iM
  have hd₁ : SmoothOfRelativeDimension h c₁.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (g₁.comp g').1 hd
  obtain ⟨P, φ, hP⟩ := GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot hL h k o ζ R₁ _ c₁ M hc₁ hd₁ hM
    (GlobalTheory.T.lam_iso_of_doubling_pullback_eq_diagonal_sq hL h k o ζ R₁ _ c₁ M hc₁ hM iM') sM
  obtain ⟨ψ, hψ'⟩ := sqOf_of_pb hP (pb_comp m' m₁)
  letI : Algebra R R₁ := ((algebraMap R' R₁).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' R₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R₁, inferInstance, inferInstance, P, ψ,
    ⟨Module.Finite.trans R' R₁, Algebra.Etale.comp R R' R₁, Module.FaithfullyFlat.trans R R' R₁⟩, ?_⟩
  have e : spMap (algebraMap R R₁) = 𝟙 _ ≫ spMap (algebraMap R' R₁) ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, ← SiegelRingChange.spMap_comp']
  rw [e]; exact hψ'

end GlobalTheory.SiegelSqrtField
end

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqrt_field : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s), c.Principal →
    ∀ (K : Type) [Field K] [CharZero K] (f : Sp K ⟶ S), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra K R₁),
      Module.Finite K R₁ ∧ Nontrivial R₁ ∧ ∃ (P : PolAV (Sp R₁)) (α : P.A.left ⟶ c.A.left) (α₂ : (G2 P.A).left ⟶ (G2 c.A).left),
        IsGrpPullback P.A c.A (spMap (algebraMap K R₁) ≫ f) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P.A P.L) (c.P.pull α₂) := by
  intro h k o _ ζ S s c hc K _ _ f
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, f ≫ s = spMap β :=
    ⟨(Spec.preimage (f ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨c₀, m₀, hc₀⟩ := pull_sieg (spMap β) f hβ c hc
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K c₀.A c₀.ab
  let c₁ : SiegPre g 2 (0 : K) (spMap (RingHom.id K)) :=
    { A := c₀.A, ab := c₀.ab, P := c₀.P, isLB := c₀.isLB, rig₁ := c₀.rig₁, rig₂ := c₀.rig₂, symm := c₀.symm,
      lev := fun _ => 1, lev_add := fun _ _ => (mul_one 1).symm, lev_tors := fun _ => one_pow _,
      geom := fun k _ _ x β' z _ hz => absurd (hz.trans (map_zero β')) z.ne_zero }
  have hc₁ : c₁.Principal := hc₀
  obtain ⟨R₁, _, _, P, φ, ⟨hfin, -, hff⟩, hP⟩ :=
    exists_sqOf_of_dim GlobalTheory.allSixLaws.1 g 2 K 0 K (RingHom.id K) c₁ hg hc₁
  obtain ⟨χ, χ₂, hχ, hs, hw, -⟩ := m₀
  obtain ⟨hφ, -, φ₂, hs', hw'⟩ := hP
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  refine ⟨R₁, inferInstance, inferInstance, hfin, ?_, P, φ ≫ χ, φ₂ ≫ χ₂, hφ.comp hχ, ⟨?_, ?_⟩, ?_⟩
  · haveI := Module.FaithfullyFlat.lTensor_nontrivial K R₁ K
    exact (TensorProduct.lid K R₁).injective.nontrivial
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans lam (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull φ₂ hw)).trans
      lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB χ₂ φ₂)

end GlobalTheory.SiegelSqrtField
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Heat.DerComm
open GlobalTheory.KS GlobalTheory.LocDerExt

theorem appLE_congr {X Y : Scheme.{0}} {g g' : Y ⟶ X} (e : g = g') (U : X.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (h' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V h = g'.appLE U V h' := by
  subst e; rfl

theorem locDerK_mono {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ W₁ : X.Opens}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D W₀ d) (hW : W₁ ≤ W₀) :
    LocDerK q p m D W₁ d :=
  ⟨fun W hW' => h.add W (hW'.trans hW), fun W hW' => h.mul W (hW'.trans hW),
   fun W W' h' hW' => h.res W W' h' (hW'.trans hW), fun W hW' => h.base W (hW'.trans hW)⟩

theorem eq_of_gen {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {V : X.Opens}
    {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDerK q p m D V d)
    (h' : LocDerK q p m D V d') {M : Type} (r : M → Γ(X, V))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ V (fun _ _ => trivial)).hom r))
    (he : ∀ j, d V (r j) = d' V (r j)) : d V = d' V := by
  funext f
  obtain ⟨P, rfl⟩ := hs f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) = a := by
      simp
    have : (p.appLE ⊤ V (fun _ _ => trivial)).hom a =
        constFn p V ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
      unfold constFn; rw [e]
    rw [this, h.base V le_rfl, h'.base V le_rfl]
  | add P Q hP hQ => rw [map_add (f := _), h.add V le_rfl, h'.add V le_rfl, hP, hQ]
  | mul_X P n hP => rw [map_mul, MvPolynomial.eval₂Hom_X', h.mul V le_rfl, h'.mul V le_rfl, hP, he]

theorem comm_of_gen : ∀ {R K : Type} [CommRing R] [Field K] {X Y : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (dl : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK q p m D ⊤ dl → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y), T₀ ≫ m = m ≫ T → T₀ ≫ q = q → T ≫ p = p → ∀ (Ix : Type) (U : Ix → X.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(X, U i)), (⨆ i, U i = ⊤) → (∀ i, IsAffineOpen (U i)) → (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (p.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) → (∀ i j, dl (T ⁻¹ᵁ U i) ((T.app (U i)).hom (r i j)) = pbT T₀ (dl (U i) (r i j)) (m ⁻¹ᵁ (T ⁻¹ᵁ U i))) → ∀ (W : X.Opens) (f : Γ(X, W)), dl (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (dl W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W)) := by
  intro R K _ _ X Y q p m D dl hdl T T₀ hm hq hp Ix U M r hU hA hs hg
  have pe : ∀ V : X.Opens, (m ≫ T) ⁻¹ᵁ V ≤ T₀ ⁻¹ᵁ (m ⁻¹ᵁ V) := fun V => by
    rw [← hm]; exact le_rfl
  have app1 : ∀ (V : X.Opens) (g : Γ(X, V)),
      (m.app (T ⁻¹ᵁ V)).hom ((T.app V).hom g) = ((m ≫ T).app V).hom g := by
    intro V g; rw [Scheme.Hom.comp_app]; rfl
  have app2 : ∀ (V : X.Opens) (g : Γ(X, V)),
      pbT T₀ ((m.app V).hom g) ((m ≫ T) ⁻¹ᵁ V) = ((m ≫ T).app V).hom g := by
    intro V g
    rw [pbT_of_le T₀ (pe V), Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    have := congrArg (fun φ => φ.hom g) (Scheme.Hom.appLE_comp_appLE T₀ m V (m ⁻¹ᵁ V) ((m ≫ T) ⁻¹ᵁ V) le_rfl (pe V))
    refine this.trans ?_
    exact congrArg (fun φ : Γ(X, V) ⟶ Γ(Y, (m ≫ T) ⁻¹ᵁ V) => φ.hom g) (appLE_congr hm V _ _ _)
  let d1 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => dl (T ⁻¹ᵁ V) ((T.app V).hom g)
  let d2 : ∀ V : X.Opens, Γ(X, V) → Γ(Y, (m ≫ T) ⁻¹ᵁ V) := fun V g => pbT T₀ (dl V g) ((m ≫ T) ⁻¹ᵁ V)
  have h1 : LocDerK q p (m ≫ T) D ⊤ d1 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d1, map_add (f := _)]; exact hdl.add _ le_top _ _
    · simp only [d1, map_mul]; rw [hdl.mul _ le_top, app1, app1]; exact rfl
    · simp only [d1]; rw [app_res T h, hdl.res _ _ _ le_top]; rfl
    · simp only [d1]
      rw [Scheme.Hom.app_eq_appLE, ← pbT_of_le T le_rfl, pbT_constFn p T le_rfl, hp]
      exact hdl.base _ le_top a
  have h2 : LocDerK q p (m ≫ T) D ⊤ d2 := by
    refine ⟨fun V _ g g' => ?_, fun V _ g g' => ?_, fun V V' h _ g => ?_, fun V _ a => ?_⟩
    · simp only [d2]; rw [hdl.add _ le_top, pbT_add]
    · simp only [d2]; rw [hdl.mul _ le_top, pbT_add, pbT_mul, pbT_mul, app2, app2]
    · simp only [d2]
      rw [hdl.res _ _ h le_top, pbT_rsT T₀ (pre_le m h) (pe V'), rsT_pbT T₀ (pe V) (pre_le (m ≫ T) h)]
    · simp only [d2]; rw [hdl.base _ le_top, pbT_constFn q T₀ (pe V), hq]
  have key : ∀ i, ∀ V, V ≤ U i → d1 V = d2 V := fun i V hV =>
    GlobalTheory.LocDerExtK.locDerK_unique (hA i) d1 d2 (locDerK_mono h1 le_top) (locDerK_mono h2 le_top)
      (eq_of_gen (locDerK_mono h1 le_top) (locDerK_mono h2 le_top) (r i) (hs i) (fun j => hg i j)) V hV
  intro W f
  show d1 W f = d2 W f
  refine eq_of_rsT_eq (fun k => (m ≫ T) ⁻¹ᵁ (W ⊓ U k)) (fun k => pre_le _ inf_le_left) ?_ _ _ ?_
  · intro y hy
    have : (m ≫ T).base y ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩
  · intro k
    rw [← h1.res W _ inf_le_left le_top, ← h2.res W _ inf_le_left le_top, key k _ inf_le_right]

end GlobalTheory.Heat.DerComm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.LiftComm

theorem appLE_congr {Z X : Scheme.{0}} {k k' : Z ⟶ X} (h : k = k') (U : X.Opens) (V : Z.Opens)
    (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V e' := by
  subst h; rfl

theorem pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens)
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT; rw [dite_eq_left h]

theorem ext_of_opens {Z X : Scheme.{0}} {a b : Z ⟶ X} (hb : a.base = b.base) (O : X.Opens → Z.Opens)
    (hO : ∀ U, O U = b ⁻¹ᵁ U)
    (h : ∀ U (e1 : O U ≤ a ⁻¹ᵁ U) (e2 : O U ≤ b ⁻¹ᵁ U), a.appLE U (O U) e1 = b.appLE U (O U) e2) :
    a = b := by
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun U e => ?_
  have key : ∀ V (_ : V = O U) (e1 : V ≤ a ⁻¹ᵁ U) (e2 : V ≤ b ⁻¹ᵁ U), a.appLE U V e1 = b.appLE U V e2 := by
    intro V hV e1 e2; subst hV; exact h U e1 e2
  rw [key _ (hO U).symm e le_rfl, Scheme.Hom.appLE_eq_app]

theorem translate_comm : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  intro k _ Y Y' X m π ρ' d Φ hb hΦ T T₀ TY h₀ h₁ h₂ hd
  have hcomp : TY ≫ ρ' ≫ m = ρ' ≫ m ≫ T := by
    rw [← Category.assoc, h₁, Category.assoc, h₀]
  have hbase : (TY ≫ Φ).base = (Φ ≫ T).base := by
    ext y
    have e := congrArg (fun g => g.base y) hcomp
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at e ⊢
    rw [hb, hb, e]
  have hle : ∀ (Z : Scheme.{0}) (V : X.Opens) (g : Z ⟶ Y'), g ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ V ≤ g ⁻¹ᵁ Φ ⁻¹ᵁ V := by
    intro Z V g y hy
    show Φ.base (g.base y) ∈ V
    rw [hb]; exact hy
  refine ext_of_opens hbase (fun W => ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) (fun W => ?_) (fun W e1 e2 => ?_)
  · exact le_antisymm (hle Y' (T ⁻¹ᵁ W) (𝟙 _)) (by
      intro y hy
      show T.base (m.base (ρ'.base y)) ∈ W
      rw [← hb]; exact hy)
  · ext f
    have hO' : ρ' ⁻¹ᵁ m ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ W := hle Y' W (𝟙 _)
    have e' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ TY ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ W :=
      le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)
    have e2' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ T ⁻¹ᵁ W := hle Y' (T ⁻¹ᵁ W) (𝟙 _)
    have hT0 : m ⁻¹ᵁ T ⁻¹ᵁ W ≤ T₀ ⁻¹ᵁ m ⁻¹ᵁ W := le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) h₀.symm)
    have hL : ((TY ≫ Φ).appLE W _ e1).hom f = (TY.appLE _ _ e').hom ((Φ.appLE W _ hO').hom f) := by
      rw [← Scheme.Hom.appLE_comp_appLE TY Φ W _ _ hO' e']; rfl
    have hR : ((Φ ≫ T).appLE W _ e2).hom f = (Φ.appLE (T ⁻¹ᵁ W) _ e2').hom ((T.app W).hom f) := by
      rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE Φ T W (T ⁻¹ᵁ W) _ le_rfl e2']; rfl
    rw [hL, hR, ← pbT_of_le Φ f _ hO', ← pbT_of_le Φ _ _ e2', hΦ, hΦ, map_add (f := _), map_mul,
      GlobalTheory.KS.DerMorK.appLE_constFn, h₂, hd]
    have a1 : pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = ((ρ' ≫ m).appLE W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom f :=
      pbT_of_le _ _ _ _
    have a2 : pbT ρ' (d W f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = (ρ'.appLE (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a3 : pbT (ρ' ≫ m) ((T.app W).hom f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        ((ρ' ≫ m).appLE (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom ((T.app W).hom f) :=
      pbT_of_le _ _ _ _
    have a4 : pbT T₀ (d W f) (m ⁻¹ᵁ T ⁻¹ᵁ W) = (T₀.appLE (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) hT0).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a5 : ∀ x : Γ(Y, m ⁻¹ᵁ T ⁻¹ᵁ W), pbT ρ' x (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        (ρ'.appLE (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom x :=
      fun x => pbT_of_le _ _ _ _
    rw [a1, a2, a3, a4, a5]
    congr 1
    · have c1 := Scheme.Hom.appLE_comp_appLE TY (ρ' ≫ m) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE (ρ' ≫ m) T W (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl le_rfl
      have c3 := appLE_congr (hcomp.trans (Category.assoc _ _ _).symm) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)) le_rfl
      rw [Scheme.Hom.app_eq_appLE]
      exact (congr(($c1).hom f)).trans ((congr(($c3).hom f)).trans (congr(($c2).hom f)).symm)
    · congr 1
      have c1 := Scheme.Hom.appLE_comp_appLE TY ρ' (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE ρ' T₀ (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) hT0 le_rfl
      have c3 := appLE_congr h₁ (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_trans e' le_rfl) (le_trans le_rfl (ρ'.preimage_mono hT0))
      exact (congr(($c1).hom (d W f))).trans ((congr(($c3).hom (d W f))).trans (congr(($c2).hom (d W f))).symm)

end GlobalTheory.KS.LiftComm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory
open Matrix

theorem exists_e8Form_value_not_dvd_prime (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (p : ℕ) (hp : p.Prime) :
    ∃ ε : Fin 8 → ℤ, ¬ (p : ℤ) ∣ ∑ u, ∑ v, W u v * ε u * ε v := by
  by_contra h
  push_neg at h
  have hQ : ∀ ε : Fin 8 → ℤ, ∑ u, ∑ v, W u v * ε u * ε v = ε ⬝ᵥ (W *ᵥ ε) := by
    intro ε
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hA : ∀ i j, (p : ℤ) ∣ (W + W.transpose) i j := by
    intro i j
    have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1)
    have h3 := h (Pi.single j 1)
    rw [hQ] at h1 h2 h3
    have e : (Pi.single i 1 + Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single j 1) = (W + W.transpose) i j := by
      simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
        single_dotProduct]
      ring
    rw [← e]
    exact dvd_sub (dvd_sub h1 h2) h3
  set A := W + W.transpose
  have hB : A = (p : ℤ) • Matrix.of (fun i j => A i j / p) := by
    ext i j
    simp [Int.mul_ediv_cancel' (hA i j)]
  have hdet : A.det = 1 := hW.2
  rw [hB, Matrix.det_smul] at hdet
  have : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by simp)) _
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem exists_e8Form_value_coprime_oddPrimePow' : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 →
    ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  intro W hW p k hp hp2
  obtain ⟨ε, hε⟩ := exists_e8Form_value_not_dvd_prime W hW p hp
  refine ⟨ε, ?_⟩
  rw [← pow_mul]
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hε (Int.natCast_dvd.2 hd)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have horbits : GlobalTheory.OrbitsInAffineOpens τ :=
    GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hs τ
  have hτg : ∀ g : Ga, (τ g).asIso.hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).asIso.hom ≫ s = s := fun g ↦ hρ g⁻¹
  have hfreeτ : GlobalTheory.IsFreeAction τ := by
    refine GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr horbits
  let sY := hQ.desc s hτs
  have hπs : π ≫ sY = s := hQ.comp_desc s hτs
  obtain ⟨hsep, hlft, hqc⟩ := isSeparated_finiteType_of_isQProjOver hs
  refine ⟨Y, π, sY, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      hQ.isFinite_of_isFreeAction hfreeτ, hQ.etale_of_isFreeAction hfreeτ, hQ.surjective, ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ := (hQ.comp_eq_comp_iff y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ sY) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated sY
  · haveI : LocallyOfFiniteType (π ≫ sY) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType sY
  · haveI : QuasiCompact (π ≫ sY) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact sY

end GlobalTheory.ZM
end
