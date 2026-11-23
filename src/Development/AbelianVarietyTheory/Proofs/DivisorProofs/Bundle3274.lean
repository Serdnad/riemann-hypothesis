module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_cmp : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hB₁ hB₂ hF₁ hF₂ hb hbβ χ₁ χ₂ hχ u hu Z x z J J₀ hJ hJ₀
  haveI : Nonempty D₁.P.A.left := nonempty_av D₁.P
  haveI : Nonempty D₂.P.A.left := nonempty_av D₂.P
  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) (Classical.arbitrary _)⟩
  haveI : Nonempty T.B.left := ⟨β₁ (Classical.arbitrary _)⟩
  have hJN : (JN D₁ D₂).IsLB := jn_isLB D₁ D₂
  have hN : (join (JN D₁ D₂) T.M.L).IsLB := join_isLB hJN T.M.isLB
  have pJ := isPart_inl (JN D₁ D₂) T.M.L
  have pT := isPart_inr (JN D₁ D₂) T.M.L
  have p₁ := pJ.trans (isPart_inl D₁.P.L D₂.P.L)
  have p₂ := pJ.trans (isPart_inr D₁.P.L D₂.P.L)
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_gen_of_iso pT p₁ w₁ hF₁.2.2.1
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_gen_of_iso pT p₂ w₂ hF₂.2.2.1
  let m₁ : D₁.P.A.left ⟶ (G2 D₁.P.A).left := (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left
  let m₂ : D₁.P.A.left ⟶ (G2 D₂.P.A).left := (lift (toUnit _ ≫ D₂.c χ₂) b).left
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨J', hJ', eJl, eJr⟩ := exists_good_join hJN T.M.isLB hJ hJ₀
  have key := gen_unique' hN (u := LB.pullGen _ _ _ t₂ m₂)
    (u' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁ m₁) (pJ.gen u)) ?fe D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A])
    (hG _ _ D₁.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ ht₂ m₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₁ m₁) (pJ.gen_isGen hu.1)) ?ev Z.left x.left z J' hJ'
  · rw [val_pull hJ', ht₂v _ _ z J' hJ', val_mul hJ', val_pull hJ', ht₁v _ _ z J' hJ', pJ.val_gen _ _ z hJ'] at key
    have e₁ : x.left ≫ m₁ = (lift (toUnit Z ≫ D₁.c χ₁) x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have e₂ : x.left ≫ m₂ = (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have r₁ : rs (M := D₁.P.L) (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) J' = rl J := by
      rw [← eJl]; funext ψ
      show Prod.fst (Prod.fst (J' (ψ ≫ coprod.inl ≫ coprod.inl))) = Prod.fst (Prod.fst (J' ((ψ ≫ coprod.inl) ≫ coprod.inl)))
      rw [Category.assoc]
    have r₂ : rs (M := D₂.P.L) (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) J' = rr J := by
      rw [← eJl]; funext ψ
      show Prod.snd (Prod.fst (J' (ψ ≫ coprod.inr ≫ coprod.inl))) = Prod.snd (Prod.fst (J' ((ψ ≫ coprod.inr) ≫ coprod.inl)))
      rw [Category.assoc]
    rw [e₁, e₂] at key
    convert key using 3 <;> first | exact r₁.symm | exact r₂.symm | exact eJl.symm | exact eJr.symm | exact congrArg₂ (isoVal w₂ _ z) eJr.symm r₂.symm | exact congrArg₂ (isoVal w₁ _ z) eJr.symm r₁.symm
  case fe =>
    have g2 : ∀ {a c : D₁.P.A.left ⟶ (G2 T.B).left}, a ≫ (fst T.B T.B).left = c ≫ (fst T.B T.B).left →
        a ≫ (snd T.B T.B).left = c ≫ (snd T.B T.B).left → a = c := fun h1 h2 => pullback.hom_ext h1 h2
    have hT0 : (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left ≫ ββ₁ = (lift (toUnit _ ≫ D₂.c χ₂) b).left ≫ ββ₂ := by
      refine g2 ?_ ?_
      · rw [Category.assoc, Category.assoc, hF₁.2.1.1, hF₂.2.1.1, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.comp_left, Over.comp_left, Category.assoc,
          Category.assoc, hF₁.2.2.2.1, hF₂.2.2.2.1, hχ]
      · rw [Category.assoc, Category.assoc, hF₁.2.1.2, hF₂.2.1.2, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, Over.id_left, Category.id_comp, hbβ]
    have hT : m₁ ≫ ββ₁ = m₂ ≫ ββ₂ := hT0
    have eT : ∀ (X : Scheme.{0}) (g : (G2 T.B).left ⟶ X), m₁ ≫ ββ₁ ≫ g = m₂ ≫ ββ₂ ≫ g := fun _ g => by
      rw [← Category.assoc, hT, Category.assoc]
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eT]
    letI := D₁.P.isAb.comm
    letI := D₂.P.isAb.comm
    have hc₁ : (toUnit D₁.P.A ≫ D₁.c χ₁) * 𝟙 D₁.P.A = 𝟙 D₁.P.A * (toUnit D₁.P.A ≫ D₁.c χ₁) := mul_comm _ _
    have hc₂ : (toUnit D₁.P.A ≫ D₂.c χ₂) * b = b * (toUnit D₁.P.A ≫ D₂.c χ₂) := mul_comm _ _
    have A1 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₁ ≫ (psum D₁.P.A (x2 D₁.P.A) a₂.down).left ≫ coprod.inl ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((𝟙 D₁.P.A * (toUnit _ ≫ D₁.c χ₁)).left ≫ coprod.inl ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₁.c χ₁).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          (h ((𝟙 D₁.P.A : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ := by
      rw [← hc₁, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₁.c χ₁) (𝟙 _) (fun g => h (g ≫ coprod.inl ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A2 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₂ ≫ (psum D₂.P.A (x2 D₂.P.A) a₂.down).left ≫ coprod.inr ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((b * (toUnit _ ≫ D₂.c χ₂)).left ≫ coprod.inr ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₂.c χ₂).left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          (h (b.left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₂.P.A).left ≫ coprod.inr ≫ coprod.inl))⁻¹ := by
      rw [← hc₂, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₂.c χ₂) b (fun g => h (g ≫ coprod.inr ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    rw [A1, A2, Fin.prod_univ_four, Fin.prod_univ_four]
    have pm : ∀ {X Y : Over (Sp V)} [GrpObj Y] (a c : X ⟶ Y), padd Y a c = a * c := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    haveI := hb
    rw [val_pull hI, ht₂v _ _ y I hI, val_mul hI, val_pull hI, ht₁v _ _ y I hI, pJ.val_gen _ _ y hI]
    have o₁ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₁.P.A) = η[D₁.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o₂ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₂.P.A) = η[D₂.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have f₁ : eSec D₁.P.A ≫ m₁ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₁.c χ₁) (1 : 𝟙_ _ ⟶ D₁.P.A)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₁]
    have f₂ : eSec D₁.P.A ≫ m₂ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₂.c χ₂) (1 : 𝟙_ _ ⟶ D₂.P.A)).left := by
      have hbη : η[D₁.P.A] ≫ b = η[D₂.P.A] := IsMonHom.one_hom b
      rw [eSec, ← Over.comp_left, comp_lift, hbη, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₂]
    rw [f₁, f₂]
    have a₂ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₂ ω s₂ e₂ β₂ ββ₂ w₂ hB₂ hF₂ (𝟙_ _) (toUnit _ ≫ D₂.c χ₂) y _ _ (pT.good hI)
      (p₂.good hI)).2
    have a₁ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₁ ω s₁ e₁ β₁ ββ₁ w₁ hB₁ hF₁ (𝟙_ _) (toUnit _ ≫ D₁.c χ₁) y _ _ (pT.good hI)
      (p₁.good hI)).2
    have c := hu.2 (𝟙_ (Over (Sp V))).left (𝟙 _) y _ (pJ.good hI)
    rw [Category.id_comp] at c
    refine a₂.trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) a₁ c).trans (_root_.mul_one 1)

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  first | exact @GlobalTheory.MumBC.refine_factor_baseChange | exact GlobalTheory.MumBC.refine_factor_baseChange | (intros; apply GlobalTheory.MumBC.refine_factor_baseChange <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PowLim.Rosati

open GlobalTheory.CechPic GlobalTheory.Mum.RosatiTens

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
  {pr : Fin r → (D'.P.A ⟶ Q.B)}

def pairQ (Q : Data R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j)

theorem cls_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) : cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (pr i) (pr j) := by
  have hC := LB.isLB_linComb Q.M.isLB (tensφ pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨w, hw⟩).trans ?_
  rw [cls_linComb Q.M.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairQ Q pr W h h := by

  rw [cls_pow w hw, pairQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

theorem pairQ_mul (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) :
    pairQ Q pr W (u * v) (u * v) = pairQ Q pr W u u + pairQ Q pr W v v + pairQ Q pr (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ pr i = u ≫ pr i * v ≫ pr i := fun i => by
    haveI := hpr i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (v ≫ pr i) (u ≫ pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairQ, hm, lam_mul_left Q.M.isLB hΘ, lam_mul_right Q.M.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

theorem comp_act_pr' (hl : IsLimit (Fan.mk D'.P.A pr)) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ PowLim.act pr hl m) ≫ pr i = ∏ k, (u ≫ pr k) ^ m i k := by
  rw [Category.assoc, PowLim.act_pr]
  exact (map_prod (pre (Z := Q.B) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := Q.B) u) _ _)

theorem pairQ_act_left (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M (u ≫ PowLim.act pr hl m) v = pairQ Q pr (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_left Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairQ_act_right (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M u (v ≫ PowLim.act pr hl m) = pairQ Q pr (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_right Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem rosatiAdj_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (h : IsUnit (W + W.transpose).det) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ i, IsMonHom (pr i)) → w.IsGen →
    ∀ a : TensO (symUnitOf W h), RosatiAdj D'.P.A D'.P.L (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a))) := by
  intro R _ _ Q D' r W h pr hl w hpr hw a
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := PowLim.act pr hl (TensO.mat _ a)
  let g := PowLim.act pr hl (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_pow w hw]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairQ_mul hpr, pairQ_mul hpr]
    rw [pairQ_act_left hl (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairQ_act_right hl (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by

        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.PowLim.Rosati

theorem GlobalTheory.Mum.PFactor.nonempty_of_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  intro R _ _ _ hR Q D' r W hpos hdet hr pr xe w hpr hlim hc hw hpsi
  let hl := hlim.some
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := PowLim.mod xe s
  obtain ⟨w', hw', htau⟩ := GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := PowLim.factor_latt xe s i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := PowLim.mod xe s
    o := { onB := { act := fun a => PowLim.act pr hl (TensO.mat s a)
                    hom := fun a => PowLim.act_isMonHom pr hl hpr _
                    map_one := PowLim.act_one pr hl
                    map_mul := fun a b => PowLim.act_mul pr hl _ _
                    map_add := fun a b => PowLim.act_add pr hl hpr _ _
                    rosati := GlobalTheory.Mum.PowLim.Rosati.rosatiAdj_pow R Q D'.toPre W hdet pr hl w hpr hw }
           c_lin := PowLim.c_smul Q D'.toPre pr hl xe hc s
           tau_bal := GlobalTheory.T.tensorData_periods_balanced_integralMatrices R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := PowLim.inc pr hl i₀
    pr := pr i₀
    xi := PowLim.xi xe i₀
    xp := PowLim.xp xe i₀
    w := w'
    idem := TensO.idem_mul_idem s i₀
    inc_hom := PowLim.inc_isMonHom pr hl hpr i₀
    pr_hom := hpr i₀
    inc_pr := PowLim.inc_pr_self pr hl i₀
    pr_inc := PowLim.pr_inc pr hl i₀
    xp_xi := hxx
    xi_xp := hxe
    c_xi := PowLim.c_xi Q D'.toPre pr hl xe hc i₀
    inj := hinj
    onto := honto
    w_gen := hw'
    tau := htau
    alg := PowLim.alg_idem_binv s i₀ hp }⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TautTransport

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem base_sq : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  intro R V _ _ _ _ f F₀ _ _ F _ _ j hj
  have e₁ : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) := by
    rw [← spMap_comp_spMap']; rfl
  have e₂ : (TF (R := V) F).hom = spMap ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) := by
    rw [← spMap_comp_spMap']; rfl
  rw [e₁, e₂, spMap_comp_spMap', spMap_comp_spMap']
  congr 1
  exact RingHom.ext fun r => hj r

theorem val_tr : ∀ {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀), letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra; ∀ (g₁ : GtPtF D₀ F), g₁.b.left = spMap j ≫ g₀.b.left → (∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) → ∀ (χ : D₀.X) (z : Sp F) J, Good D₀.P.L z J → val (g₁.s χ) (𝟙 _) z J = Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (g₀.s χ) (𝟙 _) (spMap j z) (fun ψ => J (spMap j ≫ ψ))) := by
  intro R _ _ D₀ F₀ F _ _ _ j g₀ g₁ _ hs χ z J hJ
  refine (val_corr hJ (hs χ) (𝟙 (Sp F))).trans ((val_pull hJ (g₀.s χ) (spMap j) (𝟙 (Sp F))).trans ?_)
  have e := (GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap (g₀.s χ) (spMap j) (𝟙 (Sp F₀)) hJ).symm
  rw [Category.comp_id] at e
  rw [Category.id_comp]
  exact e

theorem lamVal_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J₁ J₀ J', Good T.M.L z J₁ → Good D₀.toPre.P.L z J₀ → Good D.P.L z J' → lamVal w' p z J₁ J' = lamVal w (p ≫ sqOf (pull_grp hD)) z J₁ J₀ * ∏ I, gw hD.w (p ≫ lamφ D.P.A I) z (J₀ ((p ≫ lamφ D.P.A I) ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (J' (p ≫ lamφ D.P.A I)) ^ lamε I := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ Z p z J₁ J₀ J' hJ₁ hJ₀ hJ'
  obtain ⟨-, sq₀, gen₀, -⟩ := id h₀
  obtain ⟨-, sq₁, gen₁, -⟩ := id h₁
  obtain ⟨w'', gen'', hval⟩ := GlobalTheory.T.exists_mumfordBundleIso_comp_cartesianHom_values (pull_grp hD) (β₂ := ββ) T.M.isLB D₀.toPre.P.isLB D.P.isLB w hD.w gen₀ hD.w_gen
  have hββ : ββ' = sqOf (pull_grp hD) ≫ ββ := GlobalTheory.LamRigid.square_over_hom_ext
    (by rw [sq₁.1, Category.assoc (sqOf _), sq₀.1, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).1]; simp only [Category.assoc])
    (by rw [sq₁.2, Category.assoc (sqOf _), sq₀.2, ← Category.assoc (sqOf _), (isSquare_sqOf (pull_grp hD)).2]; simp only [Category.assoc])
  subst hββ
  refine (GlobalTheory.T.mumfordBundleIso_values_eq_of_rigidified T.M.isLB D.P.isLB D.P.isAb w' w'' gen₁ gen'' ?_ ?_ Z p z J₁ J' hJ₁ hJ').trans (hval Z p z J₁ J₀ J' hJ₁ hJ₀ hJ')
  · intro T' z' K K' hK hK'
    exact (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D (f.comp ω) (fun i => f (s i)) (hD.xe.trans e) _ _ w' hB h₁ T' 1 z' K K' hK hK').1
  · intro T' z' K K' hK hK'
    obtain ⟨K₀, hK₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := T'.left) z'
    rw [hval _ _ z' K K₀ K' hK hK₀ hK', lift_sqOf]
    have o : pushPt (pull_grp hD).1.w (1 : T' ⟶ D.P.A) = 1 := map_one (pushHom (pull_grp hD) T')
    rw [o, (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n R D₀.toPre ω s e β ββ w D₀.tau_bimult h₀ (Over.mk (T'.hom ≫ spMap f)) 1 z' K K₀ hK hK₀).1, _root_.one_mul]
    rw [prod_lam (1 : T' ⟶ D.P.A) 1 (fun q => gw hD.w q z' (K₀ (q ≫ hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f))) (K' q)), _root_.mul_one]
    simp only [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem ag {G : Type*} [CommGroup G] (A B C D v w L τ k Λ : G) (hΛ : Λ = A * B⁻¹ * C⁻¹ * D)
    (hv : w = A⁻¹ * B * C * D⁻¹ * v) (h : w = k * (L * τ)) : v = k * (L * Λ * τ) := by
  subst hΛ
  rw [hv] at h
  rw [← mul_right_inj (A⁻¹ * B * C * D⁻¹), h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tautPt_tr : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D) ββ' w', Function.Injective f → D.TauBimult → From T ω s ε n D₀.toPre e β ββ w → From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' → ∀ (F₀ : Type) [Field F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ (a : Fin T.r → ℤ) (g₀ : GtPtF D₀.toPre F₀) (g : GtPtF D F), TautPt T ω s ε n D₀.toPre e β ββ w F₀ a g₀ → Tr f hD j g₀ g → TautPt T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' F a g := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ J D₀ ω s e β ββ w f D hD ββ' w' hf hB h₀ h₁ F₀ _ _ F _ _ j hj a g₀ g hg₀ htr
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  obtain ⟨g₁, ⟨hb₁, hs₁⟩, hpull⟩ := htr
  obtain ⟨hpt₀, hv₀⟩ := hg₀
  have bsq := base_sq f F₀ F j hj
  have hπ := hpull.1
  refine ⟨?_, fun χ => ?_⟩
  · calc g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β = g₁.b.left ≫ β := by
          rw [← hπ]; simp only [Category.assoc]
      _ = spMap j ≫ g₀.b.left ≫ β := by rw [hb₁, Category.assoc]
      _ = spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω ≫ (T.c₀ a).left := by rw [hpt₀]
      _ = _ := by
          rw [← Category.assoc, bsq, Category.assoc, ← Category.assoc (spMap f), spMap_comp_spMap']
  · obtain ⟨k₀, hk₀, hv⟩ := hv₀ (hD.xe χ)
    refine ⟨Units.map j.toMonoidHom k₀, ?_, fun z J₁ J' hJ₁ hJ' => ?_⟩
    · show j (k₀ : F₀) = _
      rw [hk₀, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [map_zpow₀, hj]; rfl
    · obtain ⟨J₀, hJ₀⟩ := GlobalTheory.DegPull.exists_good' D₀.toPre.P.isLB (Z := Sp F) z
      have pv := GlobalTheory.ArcPull.pullGt_val hD hpull χ (𝟙 _) hJ₀ hJ'
      have vt := val_tr j g₀ g₁ hb₁ hs₁ (hD.xe χ) z J₀ hJ₀
      have hv' := hv (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ)) (fun ψ => hJ₁ (spMap j ≫ ψ))
        (fun ψ => hJ₀ (spMap j ≫ ψ))
      have lp := lamVal_pull T ε n R V J D₀ ω s e β ββ w f D hD ββ' w' hB h₀ h₁ _
        (lift (DegPre.cF D F χ) g.b).left z J₁ J₀ J' hJ₁ hJ₀ hJ'
      have hpq : spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left =
          (lift (DegPre.cF D F χ) g.b).left ≫ sqOf (pull_grp hD) := by
        apply GlobalTheory.LamRigid.square_over_hom_ext
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).1, ← Category.assoc _ (fst D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
          show spMap j ≫ (TF (R := R) F₀).hom ≫ (D₀.toPre.c (hD.xe χ)).left = ((TF (R := V) F).hom ≫ (D.c χ).left) ≫ _
          rw [Category.assoc, hD.c_pr χ, ← Category.assoc, ← Category.assoc, bsq]
        · rw [Category.assoc, Category.assoc, (isSquare_sqOf (pull_grp hD)).2, ← Category.assoc _ (snd D.P.A D.P.A).left,
            ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hb₁, ← hπ]
      have hsp : spMap (RingHom.id F) = 𝟙 (Sp F) := by
        simp [spMap]
      have hgm : gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn (Units.map j.toMonoidHom k₀)) := by
        rw [Category.comp_id, GlobalTheory.ArcSpecialise.gm_unitOn_spMap j k₀ z]
        have := GlobalTheory.ArcSpecialise.gm_unitOn_spMap (RingHom.id F) (Units.map j.toMonoidHom k₀) z
        rw [hsp] at this
        exact this.symm
      have m := congrArg (Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom) hv'
      have lc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (lamVal w (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ)) (fun ψ => J₀ (spMap j ≫ ψ))) = lamVal w (spMap j ≫ (lift (DegPre.cF D₀.toPre F₀ (hD.xe χ)) g₀.b).left) z J₁ J₀ :=
        (GlobalTheory.HalfBC.lamVal_comp w (spMap j) _ z J₁ J₀ hJ₁ hJ₀).symm
      have tc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) ((TF (R := R) F₀).hom ≫ spMap ω) (spMap j z) (fun ψ => J₁ (spMap j ≫ ψ))) = val (T.τ₀ ((n : ℤ) • e (hD.xe χ)) a) (spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω) z J₁ :=
        GlobalTheory.RayRosEx.ThetaPull.val_comp_stalkMap _ (spMap j) _ hJ₁
      have gc : Units.map (Scheme.Hom.stalkMap (spMap j) z).hom.toMonoidHom (gm (𝟙 (TF (R := R) F₀).left) (spMap j z) ⊤ (unitOn k₀)) = gm (spMap j ≫ 𝟙 _) z ⊤ (unitOn k₀) :=
        (GlobalTheory.ConstFam.gm_comp_stalkMap (spMap j) (𝟙 _) z ⊤ trivial _).symm
      rw [← vt, map_mul, map_mul, lc, tc, gc, hpq, hgm] at m
      have tm : spMap j ≫ (TF (R := R) F₀).hom ≫ spMap ω = (TF (R := V) F).hom ≫ spMap (f.comp ω) := by
        rw [← Category.assoc, bsq, Category.assoc, spMap_comp_spMap']
      rw [tm] at m
      have hΛ := prod_lam (DegPre.cF D F χ) g.b (fun q => GlobalTheory.ArcPull.om hD.w z J₀ J' q)
      rw [lp]
      simp only [Category.id_comp] at pv
      exact ag _ _ _ _ _ _ _ _ _ _ hΛ pv m

end GlobalTheory.TautTransport
end
end
