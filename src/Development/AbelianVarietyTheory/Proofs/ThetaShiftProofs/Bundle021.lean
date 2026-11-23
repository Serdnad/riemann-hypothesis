module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle017
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GlobalTheory.ArcPts.GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  first | exact @GlobalTheory.ArcPts.GtKer.ker_iota_torus | exact GlobalTheory.ArcPts.GtKer.ker_iota_torus | (intros; apply GlobalTheory.ArcPts.GtKer.ker_iota_torus <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcSectionValue

section General

variable {A B K : Type} [CommRing A] [CommRing B] [CommRing K] {Z : Scheme.{0}}

theorem spMap_cancel {ρ : A →+* B} (hρ : Function.Injective ρ) {f g : Sp A ⟶ Sp K}
    (h : spMap ρ ≫ f = spMap ρ ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact hρ (congrArg (fun q => q.hom a) h')

theorem valR_const (p : Z ⟶ Sp K) (f : K →+* A) (q : Sp A ⟶ Z) (hq : q ≫ p = spMap f) (U : Z.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq]
  exact Conv.valR_spMap_top f a

theorem exists_chart_local [IsLocalRing A] (x : Sp A ⟶ Z) {L : LB Z} (hL : L.IsLB) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have : x (IsLocalRing.closedPoint A) ∈ ⨆ j, L.U j := hL.cover ▸ trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨j, ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ L.U j)).1 hj).ge⟩

theorem le_div_iff {Z' : Scheme.{0}} (x : Sp A ⟶ Z') (φ : Z' ⟶ Z) (L : LB Z) (M : LB Z') (j : L.ι) (k : M.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) M).U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ M.U k :=
  ⟨fun h => ⟨fun _ hz => Set.mem_iInter.1 (h hz).1 PUnit.unit, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨Set.mem_iInter.2 fun _ => h.1 hz, h.2 hz⟩⟩

theorem exists_rigIso_of_eq {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) {L₁ L₂ : RigLB G'} (h : L₁ = L₂) (L : RigLB G)
    (w : LB.Iso L₁.L (L.L.pull m.F)) (hw : IsRigIso m L₁ L w) (k₁ : L₁.L.ι) :
    ∃ (w' : LB.Iso L₂.L (L.L.pull m.F)) (k₂ : L₂.L.ι), IsRigIso m L₂ L w' ∧ HEq k₁ k₂ ∧ L₁.L.U k₁ = L₂.L.U k₂ ∧
      ∀ (x : Sp A ⟶ G'.left) (j : L.L.ι),
        valR x _ (w.s (fun _ => j, k₁)).val = valR x _ (w'.s (fun _ => j, k₂)).val := by
  subst h
  exact ⟨w, k₁, hw, HEq.rfl, rfl, fun _ _ => rfl⟩

end General

section Germ

variable (Γ : Germs) (w : ℂ)

theorem isLocalRing_germ : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by simp [h]))
    · exact Or.inl (Γ.unit w _ h)

theorem germ_mem_convLaurent (f : Γ.R w) : (f : ℂ⸨X⸩) ∈ Conv.convLaurent := by
  obtain ⟨T, hw, a, s, hs, h⟩ := Γ.frac w f
  have hs' : (s : ℂ⸨X⸩) ≠ 0 := fun e => hs (by rw [show s = 0 from Subtype.ext e, map_zero])
  have : (f : ℂ⸨X⸩) = a / s := by rw [← h]; field_simp
  rw [this]
  exact div_mem (Conv.halfRing_le_convLaurent T a.2) (Conv.halfRing_le_convLaurent T s.2)

theorem le_of_ev {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) {U : Z.Opens}
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  haveI := isLocalRing_germ Γ w
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← IsLocalRing.comap_closedPoint (Γ.ev w).toRingHom]
  exact this

end Germ

theorem exists_le_halfPlane {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ (T' : ℝ) (h : T ≤ T'), ⊤ ≤ (spMap (Subalgebra.inclusion (Conv.halfRing_mono h) :
      Conv.halfRing T →+* Conv.halfRing T') ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  refine Conv.exists_le_preimage_inclusion yT fun p _ => ?_
  rw [hfac] at hU
  obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
    Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
  exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial

theorem exists_fsum_ne_zero {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {θ : (Fin A.gB → ℂ) → ℂ} (h : θ ≠ 0) :
    ∃ v, A.FSum 1 0 θ v ≠ 0 := by
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h
  refine ⟨(0, z), fun e => hz ?_⟩
  have hl : A.level 1 0 0 = {0} := by
    ext m
    rw [AnArc.mem_level, Finset.mem_singleton]
    have h2 := A.two_mul_exponent 1 0 m
    refine ⟨fun h0 => by_contra fun hm => ?_, fun h0 => by simp [h0, AnArc.exponent]⟩
    have := A.be_pos m hm
    simp [h0] at h2
    omega
  have := A.coeff_FSum 1 0 θ (0, z) 0
  rw [e, hl] at this
  simpa [AnArc.term] using this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_germ_lift (Y : Model Xo c β) (bF : c.F →+* ℂ) {A : AnArc (𝓞 E)} {yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c}
    (hover : yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (ΦF : GenPts A Y.oF.t yF) {Φ : GenPts A Xo.univ.t (yF ≫ pullback.fst _ _)}
    (hx : ∀ v, (ΦF.x v).left ≫ Y.m0.toSABMap.φ = (Φ.x v).left) {Γ : Germs} (Ψ : SpecPts Φ Γ)
    (U : (Xo.XF c).Opens) (hU : ⊤ ≤ yF ⁻¹ᵁ U) :
    ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → ∃ hw : Ψ.T < w.im, ∀ v, ∃ xg : Sp (Γ.R w) ⟶ Y.oF.t.G.left,
      xg ≫ Y.m0.toSABMap.φ = (Ψ.xt w hw v).left ∧ spMap (Γ.R w).val.toRingHom ≫ xg = (ΦF.x v).left ∧
      ⊤ ≤ (xg ≫ Y.oF.t.G.hom) ⁻¹ᵁ U ∧
      ∀ x : Sp ℂ ⟶ Y.oF.t.G.left, x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left →
        x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → x = spMap (Γ.ev w).toRingHom ≫ xg := by
  have hb : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) =
      yF ≫ pullback.snd _ _ := by
    rw [hover, ← spMap_comp]; rfl
  have hs : Ψ.yT ≫ Xo.s = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) ≫
      spMap (IntermediateField.inclusion c.le).toRingHom := by
    refine spMap_cancel (ρ := (Conv.halfRing Ψ.T).val.toRingHom) Subtype.val_injective ?_
    rw [← Category.assoc, Ψ.yT_gen, ← Category.assoc, hb, Category.assoc, Category.assoc, pullback.condition]
  let yT : Sp (Conv.halfRing Ψ.T) ⟶ Xo.XF c := pullback.lift _ _ hs
  have h1 : yT ≫ pullback.fst _ _ = Ψ.yT := pullback.lift_fst _ _ _
  have h2 : yT ≫ pullback.snd _ _ = spMap ((algebraMap ℂ (Conv.halfRing Ψ.T)).comp bF) := pullback.lift_snd _ _ _
  have hg : spMap (Conv.halfRing Ψ.T).val.toRingHom ≫ yT = yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, h1, Ψ.yT_gen]
    · rw [Category.assoc, h2, hb]
  obtain ⟨T₁, hT, hU₁⟩ := exists_le_halfPlane yT (hg ▸ hU)
  refine ⟨T₁, fun w hw₁ => ⟨hT.trans_lt hw₁, fun v => ?_⟩⟩
  set hw := hT.trans_lt hw₁
  have hP := Y.m0.cart.1
  have hc : (Ψ.xt w hw v).left ≫ Xo.univ.t.G.hom =
      (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ yT) ≫ pullback.fst _ _ := by
    rw [Category.assoc, h1]
    exact Over.w (Ψ.xt w hw v)
  have e1 := hP.lift_fst _ _ hc
  have e2 := hP.lift_snd _ _ hc
  refine ⟨hP.lift _ _ hc, e1, ?_, ?_, fun x hx1 hx2 => ?_⟩
  · apply hP.hom_ext
    · rw [Category.assoc, e1, Ψ.xt_gen]
      exact (hx v).symm
    · rw [Category.assoc, e2, ← Category.assoc, ← spMap_comp]
      exact hg.trans (Over.w (ΦF.x v)).symm
  · rw [e2]
    have : spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom =
        spMap (Subalgebra.inclusion (Γ.le T₁ w hw₁)).toRingHom ≫ spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) :
          Conv.halfRing Ψ.T →+* Conv.halfRing T₁) := by
      rw [← spMap_comp]; rfl
    rw [this, Category.assoc]
    exact FormalValue.top_le_comp hU₁ _
  · have e3 : x ≫ Y.m0.toSABMap.φ = (spMap (Γ.ev w).toRingHom ≫ hP.lift _ _ hc) ≫ Y.m0.toSABMap.φ := by
      rw [hx1, Ψ.pi_eq w hw v, Category.assoc]
      exact congrArg _ e1.symm
    refine hP.hom_ext e3 (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, ← hP.w, ← Category.assoc, Category.assoc _ _ (pullback.fst _ _), ← hP.w, ← Category.assoc]
      exact congrArg (· ≫ Xo.univ.t.G.hom) e3
    · rw [Category.assoc, hx2, Category.assoc, Category.assoc, reassoc_of% e2, h2, ← spMap_comp, ← spMap_comp]
      congr 1
      ext a
      exact ((Γ.ev w).commutes (bF a)).symm

end GlobalTheory.ArcSectionValue
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_germs_localRing_convergent_divisible : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  first | exact @GlobalTheory.GermRing.germs_spec | exact GlobalTheory.GermRing.germs_spec | (intros; apply GlobalTheory.GermRing.germs_spec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  first | exact @GlobalTheory.ArcPts.theta_sum_shift | exact GlobalTheory.ArcPts.theta_sum_shift | (intros; apply GlobalTheory.ArcPts.theta_sum_shift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.exists_arcGenericFibrePoints_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (F : Type) [Field F] (f : ℂ⸨X⸩ →+* F) (φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F), AnFin A → (∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v)) → ∃ Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ, (∀ v, (Θ.x v).left = spMap f ≫ (Φ.x v).left ∧ ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Θ.τ v j = f (Φ.τ v j)) ∧ ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over S) ⟶ t.G) (la : A.La) (ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩), Φ.LevelPt k (toUnit _ ≫ ξ) la → (∀ i z, IsFShift A k i.1 i.2 la z (ψ i z)) → Θ.Lev k (toUnit _ ≫ ξ) (fun i z => f (ψ i z)) := by
  first | exact @GlobalTheory.ArcBaseChange.exists_fpts_baseChange | exact GlobalTheory.ArcBaseChange.exists_fpts_baseChange | (intros; apply GlobalTheory.ArcBaseChange.exists_fpts_baseChange <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

theorem genRel_target {F : Type} [Field F] {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type}
    [Fintype K] {ε : K → ℤ} {φ : B ⟶ B'} {Φ : B' ⟶ B₀} {wD : LB.Iso M' (M₀.pull Φ)} {w' : LB.Iso M (M'.pull φ)}
    {w : LB.Iso M (M₀.pull (φ ≫ Φ))} (T : Tri wD w' w) (hM₀ : M₀.IsLB) (hM' : M'.IsLB) {pt : K → (Sp F ⟶ B)}
    {pt' : K → (Sp F ⟶ B')} {pt₀ : K → (Sp F ⟶ B₀)} (hp : ∀ k, pt k ≫ φ = pt' k) (hc : ∀ k, pt' k ≫ Φ = 𝟙 _ ≫ pt₀ k)
    {t' : LB.Gen (LB.LinComb M' pt' ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (H : PMaps wD pt' pt₀ ε t' t₀ (𝟙 _))
    (t : LB.Gen (LB.LinComb M pt ε)) (x : F) : GenRel w' t t' x ↔ GenRel w t t₀ x := by
  have z : Sp F := (default : PrimeSpectrum F)
  have pe : ∀ k, pt' k z = φ (pt k z) := fun k => congrArg (fun g => g z) (hp k).symm
  have key : ∀ (j₀ : K → M₀.ι) (i : K → M'.ι) (q : K → M.ι), (∀ k, Φ (φ (pt k z)) ∈ M₀.U (j₀ k)) →
      (∀ k, φ (pt k z) ∈ M'.U (i k)) → (∀ k, pt k z ∈ M.U (q k)) →
      (((∏ k, gw w' (pt k) z (i k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M' pt' i) (t'.s i)).val ↔
      ((∏ k, gw w (pt k) z (j₀ k) (q k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt q) (t.s q)).val =
        toStk z x * (gm (𝟙 _) z (LB.wchart M₀ pt₀ j₀) (t₀.s j₀)).val) := by
    intro j₀ i q h₀ h₁ h₂
    have a := T.prod (ε := ε) (h' := 𝟙 _) (φ' := pt') (fun k => (hp k).trans (Category.id_comp _).symm) _ (𝟙 _) z j₀ i q
      h₀ h₁ h₂
    have b := H _ (𝟙 _) z j₀ i (fun k => by show Φ (pt' k z) ∈ _; rw [pe]; exact h₀ k)
      (fun k => by show pt' k z ∈ _; rw [pe]; exact h₁ k)
    simp only [Category.id_comp] at a b
    rw [a, b, _root_.mul_assoc, Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k),
      Units.val_mul (∏ k, gw wD (pt' k) z (j₀ k) (i k) ^ ε k), mul_left_comm, Units.mul_right_inj]
  rw [genRel_iff w' t t' x z, genRel_iff w t t₀ x z]
  refine ⟨fun h => ⟨fun k => by rw [← Category.assoc, hp, hc, Category.id_comp], fun q j₀ h₀ h₂ => ?_⟩,
    fun h => ⟨hp, fun q i h₁ h₂ => ?_⟩⟩
  · choose i hi using fun k => exists_chart hM' (φ (pt k z))
    exact (key j₀ i q h₀ hi h₂).1 (h.2 q i hi h₂)
  · choose j₀ hj using fun k => exists_chart hM₀ (Φ (φ (pt k z)))
    exact (key j₀ i q hj h₁ h₂).2 (h.2 q j₀ hj h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'} {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)}
  {hD : IsPullDeg f a.D₀ a'.D₀}

section Witness

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {g : O'' →+* R} {f₀ : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}



theorem exists_witness (h : IsBC f a a' hD) (hf₀ : f₀ = g.comp f) (W : ArcWit Y a I f₀ u χ) :
    ∃ W' : ArcWit Y a' I g u χ, W'.t = W.t ∧ HEq W'.m W.m ∧ HEq W'.P W.P ∧ HEq (W'.φ ≫ proj hD) W.φ ∧
      (∀ y, HEq (W'.e y) (W.e (hD.xe y))) ∧
      ∃ w : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD)), HEq w W.w ∧ Tri hD.w W'.w w := by
  letI := H.starRing
  subst hf₀
  obtain ⟨t, m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩ := W
  have gpD := pull_grp hD
  have sq : φ ≫ a.D₀.P.A.hom = (P.D.toPre.P.A.hom ≫ spMap g) ≫ spMap f := by
    rw [s1.1.w, spMap_comp, Category.assoc]
  obtain ⟨φ', rfl, hb⟩ : ∃ φ' : P.D.toPre.P.A.left ⟶ a'.D₀.P.A.left, φ' ≫ proj hD = φ ∧
      φ' ≫ a'.D₀.P.A.hom = P.D.toPre.P.A.hom ≫ spMap g :=
    ⟨gpD.1.lift _ _ sq, gpD.1.lift_fst _ _ _, gpD.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback P.D.toPre.P.A a'.D₀.P.A (spMap g) φ' := gpD.cancel (s1.congr (spMap_comp f g) rfl) hb
  have he' : eSec P.D.toPre.P.A ≫ φ' = spMap g ≫ eSec a'.D₀.P.A := (cubeMapOf gp).e_comm
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff w).1 s2
  obtain ⟨w', T⟩ := exists_cancel a.D₀.P.isLB hD.w w gD g0 a'.D₀.P.isLB P.D.toPre.P.isLB
  have hc : ∀ y, (P.D.toPre.c (e (hD.xe y))).left ≫ φ' = spMap g ≫ (a'.D₀.c y).left := fun y => by
    refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (spMap g), ← spMap_comp]
      exact s5 _
    · rw [Category.assoc, hb, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  refine ⟨⟨t, m, P, φ', he', w', h.xeL.trans e, gp, (isGen_iff w').2 (T.pgen_cancel a.D₀.P.isLB gD g0), ?_, fun x => ?_, hc,
    fun F _ _ _ _ uF ha hu => ?_⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl, w, HEq.rfl, T⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ proj hD) (spMap (g.comp f)) he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec a.D₀.P.A) _ a'.D₀.rig a.D₀.rig (specOf f) _
      (rigPull_le (proj hD) (specOf f) hD.he a.D₀.P.L) (fun _ => rfl)).1 hD.w_rig
    rw [spMap_comp] at r₀
    exact (maps_iff w' _ (fun _ => eSec a'.D₀.P.A) _ P.D.toPre.rig a'.D₀.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' a'.D₀.P.L) (fun _ => rfl)).2 (T.pmaps_cancel a.D₀.P.isLB (fun _ => he') r₁ r₀)
  · refine gpD.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, h.act x]
      exact (s4 x).trans (Category.assoc _ _ _)
    · rw [Category.assoc, Category.assoc, Over.w, hb, ← Category.assoc, Over.w]
  · obtain ⟨_, hK, -⟩ := h.etaA 0
    letI : Algebra (FractionRing O') F :=
      ((algebraMap (FractionRing O'') F).comp (algebraMap (FractionRing O') (FractionRing O''))).toAlgebra
    have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (hK x)
    obtain ⟨k₁, k₂⟩ := s6 F uF (fun x => (hF x).trans (ha (f x))) hu
    have hj : jFK (R := R) F ≫ jK R ≫ spMap g = jFK (R := O'') F ≫ jK O'' := Compat.sq (φ := g) ha
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀' q x e1 e2 e3 e4 => ?_⟩
    · rw [h.be_eq]
      refine (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB (fun _ => ?_) (fun _ => ?_) (pmaps_psi hD F hF.sq y) _ _).2
        (k₁ (hD.xe y))
      · show (jFK (R := R) F ≫ jK R ≫ (P.D.toPre.c (e (hD.xe y))).left) ≫ φ' = jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left
        rw [Category.assoc, Category.assoc, hc, ← Category.assoc (jK R), ← Category.assoc]
        exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
      · show (jFK (R := O'') F ≫ jK O'' ≫ (a'.D₀.c y).left) ≫ proj hD =
          𝟙 _ ≫ jFK (R := O') F ≫ jK O' ≫ (a.D₀.c (hD.xe y)).left
        rw [Category.id_comp, Category.assoc, Category.assoc, hD.c_pr, ← Category.assoc (jK O''), ← Category.assoc]
        exact (congrArg (· ≫ _) hF.sq).trans (Category.assoc _ _ _)
    · obtain ⟨p, hp, hσ'⟩ : ∃ p : QkPt a.D₀ (FractionRing O') k, IsPullQk hD p p₀ ∧
          ((k = l.A ∧ ∃ v, HEq p (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
              HEq p (a.eta v) ∧ σ = Y.oF.eta v)) := by
        rcases hσ with ⟨rfl, v, h₁, h₂⟩ | ⟨rfl, v, hv, h₁, h₂⟩
        · exact ⟨a.etaA v, eq_of_heq h₁ ▸ h.etaA v, Or.inl ⟨rfl, v, HEq.rfl, h₂⟩⟩
        · exact ⟨a.eta v, eq_of_heq h₁ ▸ h.eta v, Or.inr ⟨rfl, v, hv, HEq.rfl, h₂⟩⟩
      obtain ⟨q₀, hq₀, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
      obtain ⟨hy, hg⟩ := hp.ext hF hq₀ e1
      have hy' : hD.xe q₀'.y = q₀.y := by rw [hy, AddEquiv.apply_symm_apply]
      refine k₂ yF hyF k p σ hσ' q₀ q x hq₀ (e2.trans (congrArg e hy')) (fun z => ?_) e4
      obtain ⟨z, rfl⟩ := hD.xe.surjective z
      obtain ⟨hψ, hm⟩ := hg.2 z
      have pm := (maps_iff hD.w _ _ _ (q₀'.g.s z) (q₀.g.s (hD.xe z)) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm
      have k' := e3 z
      rw [h.be_eq, hy'] at k'
      exact (genRel_target T a.D₀.P.isLB a'.D₀.P.isLB k'.1 hψ pm _ _).1 k'

end Witness

theorem exists_witness_baseChange (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (h : IsBC f a a' hD) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') {i : O' →+* R} {i' : O'' →+* R'} {κ : R →+* R'}
    (hκ : Function.Injective κ) (hI : I.map κ ≤ I') (hi : κ.comp i = i'.comp f) {u : R} {u' : R'} (hu : κ u = u')
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I i u χ) :
    ∃ (W' : ArcWit Y a' I' i' u' (spMap κ ≫ χ)) (hD₁ : IsPullDeg κ W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf κ)).obj W.t.G), IsMonHom bc.hom ∧ IsPullUnif κ hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf κ)) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ := by
  subst hu
  obtain ⟨W₁, hD₁, bc, mb, pu, hm, he, w₁, hφ, hw, T₁⟩ :=
    W.baseChange CubePf.cubePull hP hU h5 (qkPullExists hG) polOActPull hR hR' κ hκ hI
  obtain ⟨W', ht, hm', hP', hφ', he', w₂, hw', T₂⟩ := exists_witness h hi W₁
  obtain ⟨t₁, m₁, P₁, φ₁, _, _, e₁, _⟩ := W₁
  obtain ⟨t', m', P', φ', he₀, w', e', sp⟩ := W'
  dsimp only at ht
  subst ht
  obtain rfl := eq_of_heq hm'
  obtain rfl := eq_of_heq hP'
  exact ⟨⟨_, _, _, φ', he₀, w', e', sp⟩, hD₁, bc, mb, pu, hm, fun y => (congrArg hD₁.xe (eq_of_heq (he' y))).trans (he _),
    (eq_of_heq hφ').trans hφ, w₁, w₂, (hw'.trans hw).symm, T₁, T₂⟩

theorem admissibleBase_powerSeries_span_X (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    AdmBase (PowerSeries A) (Ideal.span {PowerSeries.X}) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

section PowerSeries

theorem map_comp_C' (f : O' →+* O'') :
    (PowerSeries.map f).comp (PowerSeries.C (R := O')) = (PowerSeries.C (R := O'')).comp f :=
  RingHom.ext fun x => PowerSeries.map_C f x

theorem IsBC.injective (h : IsBC f a a' hD) : Function.Injective f := by
  obtain ⟨_, hK, -⟩ := h.etaA 0
  intro x y hxy
  apply IsFractionRing.injective O' (FractionRing O')
  apply (algebraMap (FractionRing O') (FractionRing O'')).injective
  rw [hK, hK, hxy]

theorem exists_witness_powerSeries (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    [IsPrincipalIdealRing O'] [IsPrincipalIdealRing O''] (h : IsBC f a a' hD) {χ : Sp (PowerSeries O') ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ) :
    ∃ (W' : ArcWit Y a' (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O'')) PowerSeries.X
        (spMap (PowerSeries.map f) ≫ χ)) (hD₁ : IsPullDeg (PowerSeries.map f) W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (specOf (PowerSeries.map f))).obj W.t.G), IsMonHom bc.hom ∧
      IsPullUnif (PowerSeries.map f) hD₁ bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (specOf (PowerSeries.map f))) ≫ W.m.φ ∧
      (∀ y, hD₁.xe (W'.e y) = W.e (hD.xe y)) ∧ W'.φ ≫ proj hD = proj hD₁ ≫ W.φ ∧
      ∃ (w₁ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (proj hD₁ ≫ W.φ)))
        (w₂ : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull (W'.φ ≫ proj hD))),
        HEq w₁ w₂ ∧ Tri W.w hD₁.w w₁ ∧ Tri hD.w W'.w w₂ :=
  exists_witness_baseChange hG hP hU h5 h (admissibleBase_powerSeries_span_X O') (admissibleBase_powerSeries_span_X O'')
    (PowerSeries.map_injective f h.injective)
    (by rw [Ideal.map_span, Set.image_singleton, PowerSeries.map_X]) (map_comp_C' f) (PowerSeries.map_X f) W

end PowerSeries

end GlobalTheory.ArcPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GlobalTheory.ArcPts.GtAn a), (∀ z z', (Λ.ex0 z).IsAdd (Λ.ex0 z') (Λ.ex0 (z + z'))) ∧ Function.Surjective Λ.ex0 ∧ ∀ (x : 𝓞 E) z, @GtAct ℂ _ _ (𝓞 E) _ H.starRing a.D₀ ℂ _ _ _ a.oa x (Λ.ex0 z) (Λ.ex0 (Λ.A.actV x z)) := by
  first | exact @GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | exact GlobalTheory.ArcPts.ex0_additive_surjective_equivariant | (intros; apply GlobalTheory.ArcPts.ex0_additive_surjective_equivariant <;> assumption)
end
