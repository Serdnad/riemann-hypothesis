module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Limits
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι), (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).Etale := by
  intro K _ W Z Y q i π D d B α
  let E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K ≃ₐ[K] MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) :=
    (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin (B.c α).n) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv K (Fin d) (Fin (B.c α).n))
  have h : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).comp
        (E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K →+* MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K)) =
      MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, MvPolynomial.sumAlgEquiv_C_inl]
    · rintro (m | m) <;> simp [E, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have h' : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)) =
      (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t)).comp
        (E.symm : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* MvPolynomial (Fin (B.c α).n ⊕ Fin d) K) := by
    rw [← h]
    ext x
    all_goals simp
  rw [h']
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective E.symm.bijective) (B.c α).etale
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaSection :
    ∀ {σ : Type} (X : σ → Scheme.{0}) (f : ∀ p, Γ(X p, ⊤)), ∃ s : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s = f p) ∧ ∀ s' : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s' = f p) → s' = s := by
  intro σ X f
  let L := isLimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) (coproductIsCoproduct X).op
  let e : Γ(∐ X, ⊤) ≃ ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    Types.isLimitEquivSections L
  have hproj : ∀ (s : Γ(∐ X, ⊤)) (p : σ), (e s).val (Opposite.op ⟨p⟩) = (Sigma.ι X p).appTop.hom s :=
    fun s p => Types.isLimitEquivSections_apply L (Opposite.op ⟨p⟩) s
  let sec : ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    ⟨fun j => f j.unop.as, by
      rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨h⟩⟩
      cases h
      rfl⟩
  refine ⟨e.symm sec, fun p => ?_, fun s' hs' => e.injective ?_⟩
  · rw [← hproj, Equiv.apply_symm_apply]
  · apply Subtype.ext
    funext j
    obtain ⟨⟨q⟩⟩ := j
    rw [hproj, hs', Equiv.apply_symm_apply]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {V : Scheme.{0}} (a : V ⟶ ∐ X) (x : V), ∃ (U : V.Opens) (p : σ) (a₁ : (U : Scheme.{0}) ⟶ X p), x ∈ U ∧ U.ι ≫ a = a₁ ≫ Sigma.ι X p := by
  intro σ X V a x
  obtain ⟨⟨p, z⟩, hz⟩ := (sigmaMk X).surjective (a x)
  rw [sigmaMk_mk] at hz
  have hr : Set.range ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) ⊆ Set.range (Sigma.ι X p) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  refine ⟨a ⁻¹ᵁ (Sigma.ι X p).opensRange, p,
    IsOpenImmersion.lift (Sigma.ι X p) ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) hr, ?_, ?_⟩
  · show a x ∈ (Sigma.ι X p).opensRange
    exact ⟨z, hz⟩
  · exact (IsOpenImmersion.lift_fac _ _ _).symm
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {S : Scheme.{0}} {p p' : σ} (f : S ⟶ X p) (f' : S ⟶ X p') (_ : S), f ≫ Sigma.ι X p = f' ≫ Sigma.ι X p' → p = p' := by
  intro σ X S p p' f f' s h
  have e : Sigma.ι X p (f s) = Sigma.ι X p' (f' s) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact congrArg Sigma.fst ((sigmaι_eq_iff X p p' _ _).mp e)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem presheaf_map_map_eq_map {V : Scheme.{0}} {A B C : V.Opens} (i : B ⟶ A) (j : C ⟶ B)
    (k : C ⟶ A) (t : Γ(V, A)) :
    (V.presheaf.map j.op).hom ((V.presheaf.map i.op).hom t) = (V.presheaf.map k.op).hom t := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.glueSection :
    ∀ {V : Scheme.{0}} (U : V → V.Opens) (_ : ∀ x, x ∈ U x) (s : ∀ x, Γ((U x : Scheme.{0}), ⊤)), (∀ (x y : V) {S : Scheme.{0}} (f : S ⟶ (U x : Scheme.{0})) (f' : S ⟶ (U y : Scheme.{0})), f ≫ (U x).ι = f' ≫ (U y).ι → f.appTop.hom (s x) = f'.appTop.hom (s y)) → ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = s x := by
  intro V U hU s h
  have hcov : (⊤ : V.Opens) ≤ iSup U := fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  have compat : TopCat.Presheaf.IsCompatible V.sheaf.1 U (fun x => (U x).topIso.hom (s x)) := by
    intro x y
    have hc := h x y (V.homOfLE (inf_le_left : U x ⊓ U y ≤ U x)) (V.homOfLE inf_le_right)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    rw [Scheme.homOfLE_appTop, Scheme.homOfLE_appTop] at hc
    have hc' := congrArg (U x ⊓ U y).topIso.hom.hom hc
    simp only [Scheme.Opens.topIso_hom] at hc'
    have ky : U x ⊓ U y ⟶ (U y).ι ''ᵁ ⊤ := homOfLE (inf_le_right.trans (U y).ι_image_top.ge)
    exact (presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _
        (homOfLE (inf_le_left.trans (U x).ι_image_top.ge)) (s x)).trans
      ((presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _ _ (s x)).symm.trans
        (hc'.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)))
        |>.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)).symm)
  obtain ⟨s₀, hs₀, -⟩ := V.sheaf.existsUnique_gluing' U ⊤ (fun x => homOfLE le_top) hcov _ compat
  refine ⟨s₀, fun x => ?_⟩
  have e := congrArg (U x).topIso.inv.hom (hs₀ x)
  rw [Iso.hom_inv_id_apply] at e
  rw [← e, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (presheaf_map_map_eq_map (V := V) _ _ _ s₀).symm
end
