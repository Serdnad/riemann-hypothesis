module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecSpread

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [Field k] (A₀ : Over (Sp k))

theorem lbIso_lbPow_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {L : LB A₀.left} (hL : L.IsLB) (N : ℕ) :
    LBIso (lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) N)
      ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) N).pull (bcMap A₀.hom ρ)) := by
  have h₁ : LBIso (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hL _ (bcMap_fst A₀.hom ρ).symm
  have hR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow (pull_isLB hR _) N)
    (pull_isLB (isLB_lbPow hR N) _) (lbIso_lbPow h₁ N) (lbIso_lbPow_pull hR _ N)

theorem lbIso_linComb_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    {M : LB A₀.left} (hM : M.IsLB) {K : Type} [Fintype K]
    (φS : K → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))))
    (φR : K → (pullback A₀.hom (spMap (algebraMap k R)) ⟶ pullback A₀.hom (spMap (algebraMap k R))))
    (ε : K → ℤ) (hφ : ∀ o, φS o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ φR o) :
    LBIso (LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) φS ε)
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) φR ε).pull (bcMap A₀.hom ρ)) := by
  have hR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have h₁ : LBIso (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S))))
      ((M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))).pull (bcMap A₀.hom ρ)) :=
    Spread.lbIso_pull_pull hM _ (bcMap_fst A₀.hom ρ).symm
  exact LBIso.trans (LB.isLB_linComb (pull_isLB hM _) _ _) (LB.isLB_linComb (pull_isLB hR _) _ _)
    (pull_isLB (LB.isLB_linComb hR _ _) _) (PelPrim.lbIso_linComb h₁ φS ε)
    (SymExtend.lbIso_linComb_pull hR (bcMap A₀.hom ρ) φS φR ε (bcMap A₀.hom ρ) hφ)

theorem comm_bc {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S)
    (f : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)
    (g : (Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀)
    (h : bcMap A₀.hom ρ ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ g.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, Category.assoc, h]
  · have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
    have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
    rw [Category.assoc, bcMap_snd, ← Category.assoc, hf, Category.assoc, hg, bcMap_snd]

def fam {S : Type} [CommRing S] [Algebra k S] {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀)) :
    Option (Fin r) → (pullback A₀.hom (spMap (algebraMap k S)) ⟶ pullback A₀.hom (spMap (algebraMap k S))) :=
  fun o => o.elim (𝟙 _) fun i => (β i).left

theorem fam_comm {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) {r : ℕ}
    (β : Fin r → ((Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀))
    (gam : Fin r → ((Over.pullback (spMap (algebraMap k R))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k R))).obj A₀))
    (h : ∀ i, bcMap A₀.hom ρ ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _) (o : Option (Fin r)) :
    fam A₀ β o ≫ bcMap A₀.hom ρ = bcMap A₀.hom ρ ≫ fam A₀ gam o := by
  cases o with
  | none => simp [fam]
  | some i => exact comm_bc A₀ ρ (β i) (gam i) (h i)

end GlobalTheory.SqDecSpread


open GlobalTheory.Spread GlobalTheory.HomDescent GlobalTheory.SqDecSpread in
theorem GlobalTheory.SqDecSpread.sqDec_fg : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A₀ : Over (Sp k)) [GrpObj A₀],
    IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (spMap (algebraMap k Ω))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω))))
      (M.pull (pullback.fst A₀.hom (spMap (algebraMap k Ω)))) →
    ∃ R : Subalgebra k Ω, R.FG ∧ SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀)
      (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) := by
  intro k Ω _ _ _ A₀ _ hA L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have := hA.proper
  have := hA.smooth
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  choose Ri g hRi hg hgeq using fun i => haveI := hβ i; exists_fg_isMonHom (A := A₀) (A' := A₀) (β i)
  let R₁ : Subalgebra k Ω := ⨆ i, Ri i
  have hR₁ : R₁.FG := fg_iSup hRi
  choose gam hgam hgameq using fun i => haveI := hg i; exists_specialise (g i) (Subalgebra.inclusion (le_iSup Ri i))
  have key₁ : ∀ i, bcMap A₀.hom R₁.val ≫ (gam i).left ≫ pullback.fst _ _ = (β i).left ≫ pullback.fst _ _ := by
    intro i
    rw [hgameq i, ← Category.assoc, bcMap_comp_of_eq A₀.hom (Subalgebra.inclusion (le_iSup Ri i)) R₁.val (Ri i).val
      (fun _ => rfl), hgeq i]
  have hL₁ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hM₁ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R₁)))
  have hLΩ := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have hMΩ := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k Ω)))
  have H₁ : LBIso ((lbPow (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) N).pull (baseChangeMap A₀.hom R₁.val))
      ((LB.LinComb (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R₁)))) (fam A₀ gam) ε).pull
        (baseChangeMap A₀.hom R₁.val)) :=
    LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (isLB_lbPow hLΩ N) (pull_isLB (LB.isLB_linComb hM₁ _ _) _)
      (lbIso_lbPow_bc A₀ R₁.val hL N).symm
      (LBIso.trans (isLB_lbPow hLΩ N) (LB.isLB_linComb hMΩ _ _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) H
        (lbIso_linComb_bc A₀ R₁.val hM (fam A₀ β) (fam A₀ gam) ε (fam_comm A₀ R₁.val β gam key₁)))
  obtain ⟨R, hR, hRfg, H₂⟩ := exists_fg_lbIso A₀.hom hR₁ _ _ (isLB_lbPow hL₁ N) (LB.isLB_linComb hM₁ _ _) H₁
  choose δ hδ hδeq using fun i => haveI := hgam i; exists_specialise (gam i) (Subalgebra.inclusion hR)
  have hLR := pull_isLB hL (pullback.fst A₀.hom (spMap (algebraMap k R)))
  have hMR := pull_isLB hM (pullback.fst A₀.hom (spMap (algebraMap k R)))
  refine ⟨R, hRfg, N, a₀, r, a, δ, hN, ha₀, hδ, ?_⟩
  exact LBIso.trans (isLB_lbPow hLR N) (pull_isLB (isLB_lbPow hL₁ N) _) (LB.isLB_linComb hMR _ _)
    (lbIso_lbPow_bc A₀ (Subalgebra.inclusion hR) hL N)
    (LBIso.trans (pull_isLB (isLB_lbPow hL₁ N) _) (pull_isLB (LB.isLB_linComb hM₁ _ _) _) (LB.isLB_linComb hMR _ _) H₂
      (lbIso_linComb_bc A₀ (Subalgebra.inclusion hR) hM (fam A₀ δ) (fam A₀ gam) ε
        (fam_comm A₀ (Subalgebra.inclusion hR) δ gam fun i => (hδeq i).symm)).symm)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.GenFibre

theorem maximalIdeal_eq_span_of_isReduced {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) {a : R} (ha : a ≠ 0) (ha' : a ∈ maximalIdeal R)
    (hred : _root_.IsReduced (R ⧸ Ideal.span {a})) : maximalIdeal R = Ideal.span {a} := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.2 hR.le
  have hrad := (Ideal.isRadical_iff_quotient_reduced _).2 hred
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 ha')
  rw [← hrad.radical, Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP, hPp⟩
  have hne : P ≠ ⊥ := fun h => ha (by
    have := hP (Ideal.mem_span_singleton_self a)
    rwa [h, Ideal.mem_bot] at this)
  exact (IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hne)).ge

theorem isReduced_quot_of_smooth {X B : Scheme.{0}} (π : X ⟶ B) [Smooth π] (y : X) :
    _root_.IsReduced (X.presheaf.stalk y ⧸
      (maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  obtain ⟨b, z, rfl⟩ : ∃ (b : B) (z : π.fiber b), π.fiberι b z = y := ⟨π y, π.asFiber y, π.fiberι_asFiber y⟩
  have : Smooth (π.fiberToSpecResidueField b) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback π (B.fromSpecResidueField b)) ‹_›
  have : IsReduced (π.fiber b) := GlobalTheory.isReduced_of_smooth_of_isReduced (π.fiberToSpecResidueField b)
  obtain ⟨e⟩ := GlobalTheory.FibreStalk.nonempty_ringEquiv_stalk_fiber B X π b z
  exact isReduced_of_injective e.toRingHom e.injective

theorem unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (H : Over (Sp T)) [GrpObj H]
    [IsIntegral H.left], IsSemiAbelian H → ∀ y : H.left, H.hom y = closedPoint T →
    ringKrullDim (H.left.presheaf.stalk y) = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} →
    GlobalTheory.Desc.cst H.hom ϖ ≠ 0 ∧ ∀ u : H.left.functionField, u ≠ 0 → ∃ (k : ℤ) (w : H.left.functionField),
      GlobalTheory.Cartier.UnitAt y w ∧ u = GlobalTheory.Desc.cst H.hom ϖ ^ k * w := by
  intro T _ _ _ H _ _ hH y hy hdim ϖ hϖ
  have hsm : Smooth H.hom := hH.smooth
  let S := (Sp T).presheaf.stalk (H.hom y)
  letI : Algebra T S := StructureSheaf.stalkAlgebra T (H.hom y)
  haveI : (H.hom y).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  haveI : IsLocalization.AtPrime S (H.hom y).asIdeal := StructureSheaf.IsLocalization.to_stalk T _
  have hb : (H.hom y).asIdeal = maximalIdeal T := by rw [hy]; rfl
  have hmS : maximalIdeal S = Ideal.span {algebraMap T S ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (H.hom y).asIdeal S, hb, hϖ, Ideal.map_span,
      Set.image_singleton]
  let O := H.left.presheaf.stalk y
  let a₀ : O := (H.hom.stalkMap y).hom (algebraMap T S ϖ)

  have hcst : cst H.hom ϖ = algebraMap O H.left.functionField a₀ := by
    have e₁ := algebraMap_germ (X := H.left) (x := y) (U := ⊤) trivial
      (H.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ))
    have e₂ := Scheme.Hom.germ_stalkMap_apply H.hom ⊤ y trivial ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ϖ)
    refine e₁.symm.trans ?_
    refine congrArg _ (e₂.symm.trans ?_)
    rfl

  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field T (by rw [hϖ, Ideal.span_singleton_eq_bot.2 rfl])
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors
  have hs0 : algebraMap T S ϖ ≠ 0 := fun h => hϖ0 ((IsLocalization.injective S
    (H.hom y).asIdeal.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))
  have ha₀ : a₀ ≠ 0 := by
    letI : Algebra S O := (H.hom.stalkMap y).hom.toAlgebra
    haveI : Module.Flat S O := Flat.stalkMap H.hom y
    have hr : IsSMulRegular O (algebraMap T S ϖ) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs0)
    intro h
    have h1 : (algebraMap T S ϖ) • (1 : O) = (algebraMap T S ϖ) • (0 : O) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one]
      exact h
    exact one_ne_zero (hr h1)
  have ha₀m : a₀ ∈ maximalIdeal O := map_nonunit (H.hom.stalkMap y).hom _
    (hmS ▸ Ideal.mem_span_singleton_self _)

  have hred := isReduced_quot_of_smooth H.hom y
  rw [hmS, Ideal.map_span, Set.image_singleton] at hred
  have hm : maximalIdeal O = Ideal.span {a₀} :=
    maximalIdeal_eq_span_of_isReduced hdim ha₀ ha₀m hred

  haveI : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have hnf : ¬ IsField O := fun h => ha₀ (by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.1 h) ▸ ha₀m
    rwa [Ideal.mem_bot] at this)
  have hpr : Submodule.IsPrincipal (maximalIdeal O) := ⟨⟨a₀, hm⟩⟩
  haveI : IsDiscreteValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O hnf).out 1 5).2 hpr
  have hirr : Irreducible a₀ := IsDiscreteValuationRing.irreducible_iff_uniformizer a₀ |>.2 hm
  have hc : cst H.hom ϖ ≠ 0 := by
    rw [hcst]
    exact fun h => ha₀ (IsFractionRing.injective O H.left.functionField (h.trans (map_zero _).symm))
  refine ⟨hc, fun u hu => ?_⟩
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) u
  have hx : x ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hirr
  obtain ⟨n, v', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hd) hirr
  have hv' : algebraMap O H.left.functionField (v' : O) ≠ 0 :=
    (v'.isUnit.map (algebraMap O H.left.functionField)).ne_zero
  refine ⟨(m : ℤ) - n, algebraMap O _ (v : O) * (algebraMap O _ (v' : O))⁻¹,
    UnitAt.mul ⟨_, v.isUnit, rfl⟩ (UnitAt.inv ⟨_, v'.isUnit, rfl⟩), ?_⟩
  rw [hcst, zpow_sub₀ (fun h => hc (hcst.trans h)), zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
  have hc' : algebraMap O H.left.functionField a₀ ≠ 0 := hcst ▸ hc
  field_simp

end GlobalTheory.Desc.GenFibre
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.USpread

theorem lft_of_pullback {X V P S T Y : Scheme.{0}} (j : X ⟶ V) (q : V ⟶ P) (s : S ⟶ P) (t : T ⟶ S)
    (u : Y ⟶ X) (b : Y ⟶ T) [LocallyOfFiniteType j] [LocallyOfFiniteType (pullback.snd q s)]
    (h : IsPullback u b (j ≫ q) (t ≫ s)) : LocallyOfFiniteType b := by
  have h1 := (IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)
  have h2 := (IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1
  rw [← h.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem exists_to_stalk (R : Type) [CommRing R] (x : Sp R) [x.asIdeal.IsPrime] :
    ∃ t : Sp (Localization.AtPrime x.asIdeal) ⟶ Spec ((Sp R).presheaf.stalk x),
      t ≫ (Sp R).fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime x.asIdeal))) := by
  let y : PrimeSpectrum R := x
  haveI := StructureSheaf.IsLocalization.to_stalk R y
  let e := IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩
  have := Spec.fromSpecStalk_eq' (CommRingCat.of R) x
  erw [this, ← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

theorem away_finiteType (R : Type) [CommRing R] (f : R) (P A : Scheme.{0})
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (C : Type) [CommRing C] [Algebra R C] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    Algebra.FiniteType R (Localization.Away (algebraMap R C f)) := by
  let D := Localization.Away (algebraMap R C f)
  have hu : IsUnit (algebraMap R D f) := by
    rw [IsScalarTower.algebraMap_apply R C D]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away f →+* D := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D :=
    IsLocalization.Away.lift_comp f hu
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)
  have hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  have w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f := by
    rw [hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
      Spec.map_comp]
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  let l := h.lift _ _ w
  have hl : l ≫ ιA = k ≫ j := h.lift_fst _ _ w
  haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    rw [← hψ', ← h.lift_snd _ _ w]
    change LocallyOfFiniteType ((l ≫ a) ≫ _)
    infer_instance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

theorem ne_zero (R : Type) [CommRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f))
    (C : Type) [CommRing C] [Algebra R C] [Nonempty (Sp C)] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    algebraMap R C f ≠ 0 := by
  intro h0
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  obtain ⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _) (Set.range_nonempty _)
  have h1 : p y = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← hc, ← Scheme.Hom.comp_apply, hj]; rfl
  have h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t) := by
    rw [← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]; rfl
  have h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal := by
    change algebraMap R C f ∈ c.asIdeal
    rw [h0]; exact zero_mem _
  rw [← h1, h2] at h3
  exact (a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3
    (IsLocalization.Away.algebraMap_isUnit f))

theorem affine_case (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0})
    [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (x : Sp R) (V : P.Opens)
    [LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x))]
    (C : Type) [CommRing C] [IsDomain C] [Algebra R C] (j : Sp C ⟶ V) [IsOpenImmersion j]
    (hj : (j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (c : Sp C) (hc : (p ((j ≫ V.ι) c)).asIdeal ≤ x.asIdeal) :
    ∃ W : P.Opens, (j ≫ V.ι) c ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  haveI : Nonempty (Sp C) := ⟨c⟩
  haveI := x.isPrime
  have h1 := ne_zero R f P A p ιA a h C (j ≫ V.ι) hj
  have h2 := away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj
  obtain ⟨t, ht⟩ := exists_to_stalk R x
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip
  rw [← hj, ← ht, Category.assoc] at hpb
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
    (lft_of_pullback _ _ _ _ _ _ hpb)
  have h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal)
      (TensorProduct R (Localization.AtPrime x.asIdeal) C) := RingHom.finiteType_algebraMap.1 h3
  obtain ⟨g, hg, hft⟩ := GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4
  let D := Localization.Away (algebraMap R C g)
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)
  have h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← Scheme.Hom.comp_apply, hj]; rfl
  refine ⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩
  · have : c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]
      intro hgc
      apply hg
      apply hc
      rw [h5]
      exact hgc
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact ((k ≫ j) d).2
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 hft)
    have e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]
    infer_instance

theorem locally_finiteType_near : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (GlobalTheory.Desc.awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  intro R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  replace hW₀ : IsAffineOpen W₀ := hW₀
  haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩
  have hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι := by
    rw [hW₀.range_fromSpec, Scheme.Opens.range_ι]; exact hWV
  let j := IsOpenImmersion.lift V.ι hW₀.fromSpec hr
  have hj : j ≫ V.ι = hW₀.fromSpec := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW₀.fromSpec ≫ p)
  letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra
  obtain ⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hzW
  have hc' : (j ≫ V.ι) c = z := by rw [hj]; exact hc
  have := affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c
    (by erw [hc']; exact hzx)
  erw [hc'] at this
  exact this

end GlobalTheory.USpread
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

def IsConnK {R : Type} [CommRing R] {k : Type} [Field k] (A : Over (Sp R)) (L : LB A.left) (A₀ : Over (Sp k))
    (m₀ : A₀.left ⟶ A.left) (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)) : Prop :=
  GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ D' ⊤ ed ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ L.U (jj i)) ∧
    ∀ i i', ed (V i ⊓ V i') (rsT (L.g (jj i) (jj i')).val (V i ⊓ V i')) =
      pbT m₀ (L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) *
        (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))

end GlobalTheory.HeatConn
end
end
