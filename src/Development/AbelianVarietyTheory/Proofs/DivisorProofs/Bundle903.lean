module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalToGlobal.Columns.RowForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle875
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.IteratedFDeriv
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      AddMonoidAlgebra.coeff P α * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add (f := _), inner_add_right, h, h', MvPolynomial.coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, MvPolynomial.coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add (f := _), ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.ValuePullback

theorem valAt_abPull : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  intro R _ _ A F _ _ k t x fr x' fr' hx _ hv c h z J hJ
  obtain rfl : x' = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x := Over.OverMorphism.ext hx
  let p : (TFK (R := R) F).left ⟶ (TFK (R := R) (FractionRing R)).left :=
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F).left
  have e : ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ≫
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A =
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ ptSecT A.A x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x)).left ≫
      (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A).left = p ≫ (ptSecT A.A x).left :=
    congrArg (fun q => q.left) e
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_
  rw [e']
  obtain ⟨hJ', h₁, -, -⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => (snd (TFK (R := R) (FractionRing R)) A.A).left) (fun _ => (k : ℤ)) (ptSecT A.A x).left p z J hJ
  obtain ⟨-, -, h₂, h₃⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => x.left) (fun _ => (k : ℤ)) (𝟙 _) p z J hJ
  refine (h₁ _).trans ((congrArg (p.stalkMap z).hom (h (p z) _ hJ')).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ?_)))
  · refine (h₃ _).symm.trans ?_
    rw [Category.comp_id]
    refine (gs_eq p z ⊤ trivial _).trans (Eq.trans ?_ (gs_eq (𝟙 _) z ⊤ trivial _).symm)
    refine congrArg _ ?_
    exact (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) F)))).symm
  · refine (h₂ _).symm.trans (congrArg Units.val ?_)
    rw [Category.comp_id]
    have p₁ : val (powFrame A.A A.L x fr k) p z J = val fr p z J ^ (k : ℤ) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L _ fr' k) (𝟙 _) z J = val fr' (𝟙 _) z J ^ (k : ℤ) := map_zpow _ _ _
    exact p₁.trans ((congrArg (· ^ (k : ℤ)) (hv z J hJ).symm).trans p₂.symm)

end GlobalTheory.ValuePullback
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_HdR_Fil_of_field (HF : GlobalTheory.Published.AbelianDeRham.Free)
    (HH : GlobalTheory.Published.AbelianDeRham.Hodge) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧
      Module.finrank k (Fil A) = g := by
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA hg
  obtain ⟨-, -, hfin1, -, hrk1⟩ := HH k A g hA hg
  have p : PrimeSpectrum k := IsLocalRing.closedPoint k
  have h1 : Module.finrank k (primDR A) = 2 * g := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (PrimitiveSubmodule A) = g := by
    have := hrk1 p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hd : Module.finrank k (HdR A) = 2 * g := by
    change Module.finrank k (Module.Dual k (primDR A)) = 2 * g
    rw [Subspace.dual_finrank_eq, h1]
  refine ⟨?_, hd, ?_⟩
  · change FiniteDimensional k (Module.Dual k (primDR A))
    infer_instance
  · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [h2, h1] at this
    change Module.finrank k (PrimitiveSubmodule A).dualAnnihilator = g
    omega

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem periodComparison_of_gaussManinPeriods (h : GlobalTheory.Published.GaussManinPeriods) : GlobalTheory.Published.PeriodComparison := by
  obtain ⟨ε, h⟩ := h
  refine ⟨ε, fun A _ g hA hs L hL u ↦ ?_⟩
  have hp : IsGrpPullback A A (spMap ((AlgHom.id ℂ ℂ : ℂ →ₐ[ℂ] ℂ) : ℂ →+* ℂ)) (𝟙 _) :=
    haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
    (isGrpPullback_of_iso (Iso.refl A)).congr (Cris.spMap_id ℂ).symm rfl
  obtain ⟨V, u', τ, Q', Q, -, -, -, hQ, -⟩ := h ℂ A g hA hs Empty Set.univ (fun _ ↦ AlgHom.id ℂ ℂ)
    isOpen_univ trivial (fun _ ↦ differentiableOn_const _) (fun _ ↦ A) (fun _ ↦ 𝟙 _) (fun _ ↦ hp)
    (fun _ ↦ GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hp) (fun _ ↦ L) (fun _ ↦ hL)
    A (𝟙 _) hp L hL u
  exact ⟨Q, hQ⟩

end GlobalTheory.PeriodFamily
end
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
end

section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_eq_partialSum {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) {f : (I → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (I → ℂ) ℂ} (hp : HasFPowerSeriesAt f p 0) (z : I → ℂ) :
    taylor N z f = p.partialSum (N + 1) z := by
  obtain ⟨r, hr⟩ := hp
  unfold taylor FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 := hr.factorial_smul z k
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (iteratedFDeriv ℂ k f 0 fun _ ↦ z) =
      ∑ s : Fin k → I, (∏ a, z (s a)) • iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1 := by
    have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • (Pi.single i (1 : ℂ) : I → ℂ) := by
      funext a j
      simp [Finset.sum_apply, Pi.single_apply]

    rw [hz, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h2, nsmul_eq_mul] at h1
  rw [← inv_mul_cancel_left₀ hk (p k fun _ ↦ z), h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_eq_mul]
  ring

theorem diag_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) {f : E → ℂ}
    {p : FormalMultilinearSeries ℂ E ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) (k : ℕ) : k ≤ N → ∀ y, (p k fun _ ↦ y) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hp.isBigO_sub_partialSum_pow (k + 1)
    have hs : ∀ y, p.partialSum (k + 1) y = p k fun _ ↦ y := by
      intro y
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj ↦ ih j (Finset.mem_range.1 hj)
          (le_trans (Finset.mem_range.1 hj).le hk) y, zero_add]
    have h2 : (fun z : E ↦ ‖z‖ ^ (N + 1)) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_of_le_one (norm_nonneg _) (by simpa using hz) (by omega)
    have h3 : (fun y : E ↦ p k fun _ ↦ y) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine ((hf.trans h2).sub h1).congr_left fun y ↦ ?_
      simp [hs]
    exact h3.continuousMultilinearMap_apply_eq_zero

theorem iteratedFDeriv_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ)
    {f : E → ℂ} (ha : AnalyticAt ℂ f 0) (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) {k : ℕ} (hk : k ≤ N)
    (v : Fin k → E) : iteratedFDeriv ℂ k f 0 v = 0 := by
  obtain ⟨p, hp⟩ := ha
  have h := diag_eq_zero_of_isBigO N hp hf k hk
  obtain ⟨r, hr⟩ := hp
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace, ← (p k).iteratedFDeriv_comp_diagonal 0 v]
  simp [h]

theorem taylor_remainder_and_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  intro I _ _ N f ha
  refine ⟨?_, fun hf D _ _ t ↦ ?_⟩
  · obtain ⟨p, hp⟩ := ha
    refine (hp.isBigO_sub_partialSum_pow (N + 1)).congr_left fun z ↦ ?_
    rw [taylor_eq_partialSum N hp, zero_add]
  · unfold taylor
    refine Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_eq_zero_of_isBigO N ha hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero,
      zero_smul]

end GlobalTheory.PeriodFamily
end

section

noncomputable section

namespace GlobalTheory.LossItemsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HCEntries

section Programme

variable {l d : ℕ} [NeZero d]

end Programme

section Point

variable {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC}

theorem cube_le_eta (P : ParameterChoice' D L) : 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 ≤ L.etaSz := by
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have a1 := P.h0_ge.2.2.2.2.1
  have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
  linarith [one_le_letterBlockLength D]

end Point

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.LossItemsCompare

end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.rowLevel_principal_firstBlock_index_eq_card : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  exact @GlobalTheory.RowLevIndex.index_eq
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_integralClosure_pi_of_etale : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (E : ι → Type) [∀ i, CommRing (E i)]
    [∀ i, Algebra R (E i)], (∀ i, Algebra.Etale R (integralClosure R (E i))) →
    Algebra.Etale R (integralClosure R (∀ i, E i)) := by
  first | (exact @GlobalTheory.PiClosure.etale_integralClosure_pi) | (exact GlobalTheory.PiClosure.etale_integralClosure_pi) | (intros; apply GlobalTheory.PiClosure.etale_integralClosure_pi  <;> assumption)
end
