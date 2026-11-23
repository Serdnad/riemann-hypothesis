module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LiftZPMapAeval
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGaugeBilinearTermOfTypeNe
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValEqSelf
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelLift

private theorem formallySmooth_stalk {B : CommRingCat.{0}} {X : Scheme.{0}} (s : X ⟶ Spec B) [Smooth s] (y : X) :
    ∃ α : B ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ s := by
  let τ : B ⟶ (Spec B).presheaf.stalk (s y) := StructureSheaf.toStalk B (s y)
  refine ⟨τ ≫ s.stalkMap y, ?_, ?_⟩
  · have hs : (s.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (s.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra B ((Spec B).presheaf.stalk (s y)) := StructureSheaf.stalkAlgebra B (s y)
    have := (s y).isPrime
    have : IsLocalization.AtPrime ((Spec B).presheaf.stalk (s y)) (s y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk B (s y)
    have h₀ : Algebra.FormallySmooth B ((Spec B).presheaf.stalk (s y)) :=
      Algebra.FormallySmooth.of_isLocalization (s y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec B).fromSpecStalk (s y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]

private theorem ring_lift {B A O R' : Type} [CommRing B] [CommRing A] [CommRing O] [CommRing R'] (α : B →+* A)
    (hα : α.FormallySmooth) (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (χ : A →+* O) (hc : χ.comp α = π.comp β') :
    ∃ χ' : A →+* R', π.comp χ' = χ ∧ χ'.comp α = β' := by
  letI := α.toAlgebra
  letI := β'.toAlgebra
  letI := (π.comp β').toAlgebra
  haveI : Algebra.FormallySmooth B A := hα
  let π₁ : R' →ₐ[B] O := { π with commutes' := fun _ => rfl }
  let χ₁ : A →ₐ[B] O := { χ with commutes' := fun b => RingHom.congr_fun hc b }
  have hn : IsNilpotent (RingHom.ker (π₁ : R' →+* O)) := ⟨2, hk⟩
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn : A →+* R'), RingHom.ext fun a => ?_,
    RingHom.ext fun b => (Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn).commutes b⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply χ₁ π₁ hs hn a

private theorem point_lift {B O R' : Type} [CommRing B] [CommRing O] [IsLocalRing O] [CommRing R'] {X : Scheme.{0}}
    (s : X ⟶ Geo.Tor.Sp B) [Smooth s] (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (f : Geo.Tor.Sp O ⟶ X) (hf : f ≫ s = Geo.Tor.spMap (π.comp β')) :
    ∃ f' : Geo.Tor.Sp R' ⟶ X, f' ≫ s = Geo.Tor.spMap β' ∧ Geo.Tor.spMap π ≫ f' = f := by
  obtain ⟨α, hα, e⟩ := formallySmooth_stalk s (f (IsLocalRing.closedPoint O))
  have hχ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of O) f
  have hc : α ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of O) f = CommRingCat.ofHom (π.comp β') := by
    apply Spec.map_injective
    rw [Spec.map_comp, e, ← Category.assoc, hχ, hf]
  obtain ⟨χ', h₁, h₂⟩ := ring_lift α.hom hα π hs hk β' (Scheme.stalkClosedPointTo (R := CommRingCat.of O) f).hom
    (congrArg (fun g => g.hom) hc)
  refine ⟨Spec.map (CommRingCat.ofHom χ') ≫ X.fromSpecStalk _, ?_, ?_⟩
  · rw [Category.assoc, ← e, ← Spec.map_comp, ← h₂]
    rfl
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h₁]
    exact hχ

theorem exists_principal_lift : ∀ (h p M : ℕ) (Ag : Geo.Tor.SiegelFamily h p M), GlobalTheory.ZM.SRep Ag → M.Coprime p → M ≠ 0 → ∀ (O R' : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ β : Geo.Tor.ZP p M →+* O, Function.Injective β → ∀ c : Geo.Tor.SiegPre h M (Geo.Tor.zetaZP p M) (Geo.Tor.spMap β), c.Principal → ∃ (β' : Geo.Tor.ZP p M →+* R') (c' : Geo.Tor.SiegPre h M (Geo.Tor.zetaZP p M) (Geo.Tor.spMap β')), c'.Principal ∧ Geo.Tor.SiegPB c c' (Geo.Tor.spMap π) := by
  intro h p M Ag hA hMp hM O R' _ _ _ _ π hs hk β hβ c hc
  have hd : Dense {x : Geo.Tor.Sp O | (Geo.Tor.spMap β x).asIdeal = ⊥} := by
    have h0 : Dense ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)} : Set (PrimeSpectrum O)) := by
      rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    refine h0.mono ?_
    rintro _ rfl
    exact (RingHom.injective_iff_ker_eq_bot β).1 hβ
  obtain ⟨f, hf, hcf⟩ := hA.2 _ _ c inferInstance hd hc
  obtain ⟨β', rfl⟩ := GlobalTheory.zp_lift_sqZero p M R' O π hs hk hMp hM β
  have : Smooth Ag.s := have := Ag.smooth; SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) _
  obtain ⟨f', hf', e⟩ := point_lift Ag.s π hs hk β' f hf
  obtain ⟨⟨c', hc'⟩, hp⟩ := GlobalTheory.siegPre_pullback h M _ _ _ _ _ _ f' Ag.univ hf'
  exact ⟨β', c', hp c' hc' Ag.princ, GlobalTheory.SiegelPullComp.pb_cancel hc' (by rw [e]; exact hcf)⟩

end GlobalTheory.SiegelLift
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, HasTeich X V g → ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)) := by
  first | exact @GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | exact GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne | (intros; apply GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne <;> assumption)
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.valEqSelfSt_of_hyps : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ), ValEqSelfSt Y p H Ls n := by
  first | exact @GlobalTheory.ValSelf.valEqSelf | exact GlobalTheory.ValSelf.valEqSelf | (intros; apply GlobalTheory.ValSelf.valEqSelf <;> assumption)
end

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

theorem _root_.GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  first | exact @GlobalTheory.nabValN_eq_sum_coeff | exact GlobalTheory.nabValN_eq_sum_coeff | (intros; apply GlobalTheory.nabValN_eq_sum_coeff <;> assumption)
end
