module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2265
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.TInj.FromRefine

theorem from_of_refines : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ ρ ω s Q e D e' hρ hDF hR
  obtain ⟨βQ, β₂Q, wQ, pbQ, sqQ, genQ, cQ, τQ⟩ := hDF
  obtain ⟨βR, β₂R, wR, pbR, sqR, genR, cR, τR⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w'', hT⟩ := exists_comp hΛQ wQ wR ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR) hΛT hΛD
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J JQ J', Good T.M.L z J → Good Q.M.L z JQ →
      Good D.P.L z J' → lamVal w'' p z J J' = lamVal wQ (p ≫ β₂R) z J JQ * lamVal wR p z JQ J' := by
    intro Z p z J JQ J' hJ hJQ hJ'
    have t := hT Z p z (fun I => J (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (Set.mem_iInter.2 fun I => hJQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw wQ (p ≫ β₂R) z (fun I => J ((p ≫ β₂R) ≫ β₂Q ≫ lamφ T.B I))
        (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      simp only [Category.assoc]
    · show _ = gw wR p z (fun I => JQ (p ≫ β₂R ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      simp only [Category.assoc]
  refine ⟨βR ≫ βQ, β₂R ≫ β₂Q, w'', ?_, isSquare_comp sqR sqQ,
    (isGen_iff _).2 (hT.pgen_comp hΛQ ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR)), ?_, ?_⟩
  · exact (IsGrpPullback.comp pbR pbQ).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω ρ) rfl
  · intro a
    show (D.c a).left ≫ βR ≫ βQ = spMap (ρ.comp ω) ≫ (T.c₀ ((n : ℤ) • e (e' a))).left
    rw [← Category.assoc, cR, Category.assoc, cQ, ← Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  · intro a b
    obtain ⟨k, hk, hv⟩ := τQ (e' a) (e' b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) ρ (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
    have hm : ∀ r, m (algebraMap R _ r) = algebraMap V _ (ρ r) := fun r => IsLocalization.map_eq _ _
    let κ : (TK V).left ⟶ (TK R).left := spMap m
    have hκ : κ ≫ jK R = jK V ≫ spMap ρ := GlobalTheory.HalfBC.gam_comm ρ m hm
    refine ⟨Units.map m.toMonoidHom k, ?_, fun z J J' hJ hJ' => ?_⟩
    · rw [Units.coe_map]
      show m (k : FractionRing R) = _
      rw [hk, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · choose JQ hJQ0 using fun χ : (TK V).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
      have hJQ : Good Q.M.L z JQ := hJQ0
      have r1 := τR κ hκ a b z JQ J' hJQ hJ'
      have nQ : val (Q.tau (e' a) (e' b)) (κ ≫ 𝟙 _) z JQ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (Q.tau (e' a) (e' b)) (𝟙 _) (κ z) (fun ψ => JQ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z JQ hJQ).2.2.1 _)
      rw [Category.comp_id] at nQ
      have r2 := hv (κ z) (fun ψ => J (κ ≫ ψ)) (fun ψ => JQ (κ ≫ ψ)) (fun ψ => hJ (κ ≫ ψ)) (fun ψ => hJQ (κ ≫ ψ))
      rw [r2, map_mul, map_mul] at nQ
      have g1 : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 _) (κ z) ⊤ (unitOn k)) =
          gm (𝟙 _) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact GlobalTheory.PolDeg.gm_spMap_unitOn m k z
      have g2 := (GlobalTheory.HalfBC.lamVal_comp wQ κ
        (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left z J JQ hJ hJQ).symm
      have g3 : Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => J (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) (κ ≫ (TK R).hom ≫ spMap ω) z J :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ ((TK R).hom ≫ spMap ω) κ z J hJ).2.2.1 _)).symm
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ βR = κ ≫ (toUnit (TK R) ≫ Q.c (e' χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ βR = κ ≫ jK R ≫ (Q.c (e' χ)).left
        rw [Category.assoc, cR, ← Category.assoc, ← hκ, Category.assoc]
      have hP : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂R =
          κ ≫ (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left := by
        apply pullback.hom_ext
        · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
          rw [Category.assoc, sqR.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
            ← Over.comp_left, lift_fst]
          exact hx a
        · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
          rw [Category.assoc, sqR.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
            ← Over.comp_left, lift_snd]
          exact hx b
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (ρ.comp ω) := by
        rw [← GlobalTheory.HalfBC.spMap_comp_spMap', ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ spMap ω) hκ
      rw [g1, g2, g3, ← hP, hb] at nQ
      rw [r1, nQ, key _ _ z J JQ J' hJ hJQ hJ']
      ac_rfl

end GlobalTheory.TInj.FromRefine
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatBase

theorem nsmul_b' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, rfl⟩ := H
  have : ∀ i : Fin (k + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero]; exact h0.1
    | succ i ih => rw [(hs i).1, ih, Fin.val_succ, pow_succ]; rfl
  exact this _

theorem pow_comp' {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem ratBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ _ Q e hD hT D' F p₀ p hy hg
  haveI := F.inc_hom
  haveI := F.pr_hom
  set L := AlgebraicClosure (FractionRing R)
  set a := F.xp p₀.y
  let b₀ : TF (R := R) L ⟶ Q.B := p₀.g.b ≫ F.pr
  have hpb : p.g.b = b₀ ≫ F.inc := by rw [hg.1, ← F.pr_inc, Category.assoc]
  obtain ⟨h, h1, h2⟩ := p₀.eq
  have hn1 : p₀.g.b ^ n = toUnit _ ≫ D'.toPre.c p₀.y := (nsmul_b' h1).symm.trans h2.1
  have hcpr : D'.toPre.c p₀.y ≫ F.pr = Q.c a := by
    have h3 : D'.toPre.c p₀.y ≫ F.pr ≫ F.inc = Q.c a ≫ F.inc := by
      rw [F.pr_inc, ← F.o.c_lin, ← F.xi_xp, F.c_xi]
    have h4 := congrArg (· ≫ F.pr) h3
    simpa only [Category.assoc, F.inc_pr, Category.comp_id] using h4
  have hb₀ : b₀ ^ n = toUnit _ ≫ Q.c a := by
    rw [← pow_comp', hn1, Category.assoc, hcpr]
  obtain ⟨β, β₂, w, hpb', hsq, hw, hc, htau⟩ := hD

  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb'.1.lift _ _ hcomm) (by simpa using hpb'.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb'.1.lift_fst _ _ hcomm
  have hdn : d ^ n = Q.c a := by
    refine Over.OverMorphism.ext (hpb'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [GlobalTheory.FrameMove.pow_comm hpb' hd n, hc a]
    congr 2
    have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
    exact (key n).symm

  let κ := algebraMap (FractionRing R) L
  let x : TF (R := R) L ⟶ Q.B := b₀ * (toUnit _ ≫ d)⁻¹
  have hx : x ^ n = 1 := by
    simp only [x]
    rw [mul_pow, inv_pow, hb₀, ← GlobalTheory.FrameMove.comp_pow, hdn, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := hT L κ x hx
  let ρ : TF (R := R) L ⟶ TK R := Over.homMk (spMap κ) rfl
  have hxρ : x = ρ ≫ x₀ := Over.OverMorphism.ext hx₀
  have hb₀' : b₀ = ρ ≫ (x₀ * (toUnit _ ≫ d)) := by
    rw [MonObj.comp_mul, ← hxρ, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
    simp only [x, inv_mul_cancel_right]
  let σ : TF (R := R) (FractionRing R) ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  refine ⟨σ ≫ (x₀ * (toUnit _ ≫ d)) ≫ F.inc, ?_⟩
  rw [hpb, hb₀']
  simp only [Over.comp_left]

  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : σ.left = 𝟙 _ := hj
  rw [hσ, Category.id_comp, Category.assoc]
  rfl

end GlobalTheory.Mum.RatBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ETors

open GlobalTheory.BXOf GlobalTheory.TorusExt ReciprocityTheory.ChartRestriction.G.DVR

theorem cubN_pow_eq_pow {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (P : Subgroup A)
    (H : Subgroup U) (hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, θ x y z ∈ H) {n : ℕ} {b d : A} (hb : b ∈ P) (hd : d ∈ P)
    (hn : b ^ n = 1) : ∃ h ∈ H, cubN θ n 1 b (d ^ n) = h ^ n := by
  have hN : cubN θ n 1 b d ∈ H := H.prod_mem fun i _ => hθ _ (P.mul_mem P.one_mem (P.pow_mem hb i)) _ hb _ hd
  have key : ∀ j : ℕ, ∃ r ∈ H, cubN θ n 1 b (d ^ j) = cubN θ n 1 b d ^ j * r ^ n := by
    intro j
    induction j with
    | zero => exact ⟨1, H.one_mem, by rw [pow_zero, C.N_one]; simp⟩
    | succ j ih =>
      obtain ⟨r, hr, e⟩ := ih
      have a := C.N_add n 1 b (d ^ j) d
      rw [hn, _root_.mul_one (1 : A), C.face, _root_.mul_one, _root_.one_mul, e, ← pow_succ] at a
      refine ⟨r * (θ b (d ^ j) d)⁻¹, H.mul_mem hr (H.inv_mem (hθ _ hb _ (P.pow_mem hd j) _ hd)), ?_⟩
      rw [eq_mul_inv_of_mul_eq a, mul_pow, inv_pow, pow_succ (cubN θ n 1 b d), ← _root_.mul_assoc,
        mul_right_comm (cubN θ n 1 b d ^ j)]
  obtain ⟨r, hr, e⟩ := key n
  exact ⟨_ * r, H.mul_mem hN hr, by rw [e, mul_pow]⟩

theorem sig_val_fixed {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {F : Type} [Field F] (σ : F →+* F)
    {J : (Spec (CommRingCat.of F) ⟶ X) → L.ι} (hJ : Good L (closedPoint F) J) (r : Spec (CommRingCat.of F) ⟶ Y)
    (hr : Spec.map (CommRingCat.ofHom σ) ≫ r = r) :
    Units.map σ.toMonoidHom (sig F (val t r (closedPoint F) J)) = sig F (val t r (closedPoint F) J) := by
  have e := val_nat ht σ hJ hJ r
  have hdel : ∀ k, GlobalTheory.BXOf.del L σ J J (r ≫ φ k) = 1 := fun k => by
    rw [← del_id hL hJ (r ≫ φ k)]
    unfold GlobalTheory.BXOf.del
    rw [← Category.assoc, hr, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [hr, Finset.prod_eq_one (fun k _ => by rw [hdel, one_zpow]), _root_.one_mul] at e
  exact e.symm

theorem exists_c_eq_pow {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {R : Type} [CommRing R]
    [IsDomain R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (h : DataFrom T iw s ε n Q e) (a : Q.X) :
    ∃ d : 𝟙_ (Over (Sp R)) ⟶ Q.B, Q.c a = d ^ n := by
  obtain ⟨β, -, -, ⟨g, gm⟩, -, -, c, -⟩ := h
  let x : (Fin T.r → ℤ) → (Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap iw) ⟶ T.B) := fun v => toUnit _ ≫ T.c₀ v
  have xl : ∀ v, (x v).left = spMap iw ≫ (T.c₀ v).left := fun v => by
    show (𝟙 _ ≫ spMap iw) ≫ _ = _
    rw [Category.id_comp]
  have xa : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    show toUnit _ ≫ T.c₀ (v + v') = _
    rw [T.c₀_add]; exact MonObj.comp_mul _ _ _
  have w : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 _ ≫ spMap iw := by
    rw [Category.assoc, Over.w]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (g.lift _ _ w) (g.lift_snd _ _ w)
  have hd : (x (e a)).left = d.left ≫ β := (xl _).trans (g.lift_fst _ _ w).symm
  have key : ∀ k : ℕ, (x (((k + 1 : ℕ) : ℤ) • e a)).left = (d ^ (k + 1)).left ≫ β := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [Nat.cast_succ (k + 1), add_smul, one_smul, xa, pow_succ d (k + 1)]
      exact gm _ _ _ _ _ ih hd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨d, Over.OverMorphism.ext (g.hom_ext ?_ ?_)⟩
  · rw [c, ← key, xl]
  · rw [Over.w, Over.w]

attribute [local instance] gtGroup

theorem charVal_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) (k : ℕ) :
    charVal (k • t) χ y J * cubN (th D y J) k 1 t.b (cP D _ χ) = charVal t χ y J ^ k := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  induction k with
  | zero => rw [zero_nsmul, zero_val χ hJ]; simp [cubN]
  | succ k ih =>
    have a := add_val (k • t) t χ hJ
    rw [nsmul_b, C.s01, C.s12] at a
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [succ_nsmul, pow_succ, ← ih, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, a, mul_right_comm]

theorem corr_pullGen_of_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)), ∀ t : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtAct F.o F.e t t → (∃ z : GtPtF D'.toPre (AlgebraicClosure (FractionRing R)), GtPtF.IsNsmul n t z ∧ z.IsZero) → spMap σ.toAlgHom.toRingHom ≫ t.b.left = t.b.left → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (t.s χ) (LB.pullGen D'.toPre.P.L _ _ (t.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ hζ Q e hQ _ D' F σ t ht ⟨z, hz, hz0⟩ hb
  set K := AlgebraicClosure (FractionRing R) with hK
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) K :=
    RingHom.ext fun x => σ.commutes x
  have hnt : n • t = 0 := ((isNsmul_iff_eq _ _ _).1 hz).symm.trans ((isZero_iff_eq _).1 hz0)
  choose J hJ using fun ψ : (TF (R := R) K).left ⟶ D'.toPre.P.A.left =>
    exists_chart D'.toPre.P.isLB (ψ (closedPoint K))
  replace hJ : Good D'.toPre.P.L (Z := (TF (R := R) K).left) (closedPoint K) J := hJ
  suffices H : ∀ χ, σ.toAlgHom.toRingHom (sig K (charVal t χ (closedPoint K) J) : K) =
      (sig K (charVal t χ (closedPoint K) J) : K) from
    ((eq_gtExt_iff _ hσ t t).1 (gtExt_eq_self_of_charVal_fixed R D'.toPre K _ hσ t hb J hJ H).symm).2
  let H : Subgroup ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ :=
    MonoidHom.eqLocus ((Units.map σ.toAlgHom.toRingHom.toMonoidHom).comp (sig K)) (sig K)
  let P : Subgroup (TF (R := R) K ⟶ D'.toPre.P.A) :=
    { carrier := {x | extMap _ hσ ≫ x = x}
      mul_mem' := fun {a b} ha hb => (MonObj.comp_mul _ _ _).trans (congrArg₂ (· * ·) ha hb)
      one_mem' := MonObj.comp_one _
      inv_mem' := fun {a} ha => (GrpObj.comp_inv _ _).trans (congrArg (·⁻¹) ha) }
  have hP : ∀ d : 𝟙_ (Over (Sp R)) ⟶ D'.toPre.P.A, toUnit _ ≫ d ∈ P := fun d => by
    show extMap _ hσ ≫ toUnit _ ≫ d = toUnit _ ≫ d
    rw [← Category.assoc, toUnit_unique (extMap _ hσ ≫ toUnit _) (toUnit _)]
  have hbP : t.b ∈ P := Over.OverMorphism.ext hb
  have hθ : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, th D'.toPre (T := TF (R := R) K) (closedPoint K) J x y z ∈ H := by
    intro x hx y hy z hz
    refine sig_val_fixed D'.toPre.P.isLB D'.toPre.cub.isGen _ hJ (lift x (lift y z)).left ?_
    show (extMap _ hσ ≫ lift x (lift y z)).left = _
    rw [comp_lift, comp_lift, hx, hy, hz]
  have C : IsCub (th D'.toPre (T := TF (R := R) K) (closedPoint K) J) := isCub_cubV D'.toPre.cub hJ

  have := F.o.onB.hom F.e
  have := F.o.onB.hom (star F.e)
  have := F.o.onB.hom F.f
  have := F.inc_hom
  have hr := F.o.onB.rosati (star F.e)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros GlobalTheory.SemiRigid.globalFns D'.toPre.P.isAb D'.toPre.P.isLB _ _ hr
  have rel : ∀ χ, ∃ h ∈ H, charVal t χ (closedPoint K) J = charVal t (star F.e • χ) (closedPoint K) J * h := by
    intro χ
    refine ⟨val u (lift (cP D'.toPre _ χ) t.b).left (closedPoint K) J, ?_, ?_⟩
    · refine sig_val_fixed D'.toPre.P.isLB hu _ hJ (lift (cP D'.toPre _ χ) t.b).left ?_
      show (extMap _ hσ ≫ lift (cP D'.toPre _ χ) t.b).left = _
      rw [comp_lift, comp_cP, hbP]
    · refine (val_corr hJ (ht.2 u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      rw [val_pull hJ, Category.id_comp]; rfl

  have root : ∀ w : ((TF (R := R) K).left.presheaf.stalk (closedPoint K))ˣ, w ^ n = 1 → w ∈ H := by
    intro w hw
    have hinj : Function.Injective ((algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))) :=
      (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)
    have hζ' := hζ.map_of_injective hinj
    have : NeZero n := ⟨by omega⟩
    have hw' : (sig K w : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw'
    have e : σ (sig K w : K) = (sig K w : K) :=
      (congrArg σ hi.symm).trans ((map_pow σ _ i).trans ((congrArg (· ^ i) (σ.commutes _)).trans hi))
    exact Units.ext e

  have img : ∀ a : Q.X, charVal t (F.f • F.xi a) (closedPoint K) J ∈ H := by
    intro a
    obtain ⟨d, hd⟩ := exists_c_eq_pow T iw s ε hn Q e hQ a
    have hc : cP D'.toPre (TF (R := R) K) (F.f • F.xi a) = (toUnit _ ≫ (d ≫ F.inc) ≫ F.o.onB.act F.f) ^ n := by
      rw [cP, F.o.c_lin, F.c_xi, hd, MonObj.pow_comp, MonObj.pow_comp, MonObj.comp_pow]
    have hbn : t.b ^ n = 1 := by rw [← nsmul_b, hnt, zero_b]
    obtain ⟨h, hh, e₁⟩ := cubN_pow_eq_pow C P H hθ hbP (hP ((d ≫ F.inc) ≫ F.o.onB.act F.f)) hbn
    have e₂ := charVal_pow t (F.f • F.xi a) hJ n
    rw [hnt, zero_val (D := D'.toPre) (F := K) _ hJ, _root_.one_mul, hc, e₁] at e₂
    have := H.mul_mem (root (charVal t (F.f • F.xi a) (closedPoint K) J * h⁻¹)
      (by rw [mul_pow, ← e₂, inv_pow, mul_inv_cancel])) hh
    rwa [inv_mul_cancel_right] at this
  intro χ
  obtain ⟨a, ha⟩ := F.onto χ
  obtain ⟨h, hh, e₁⟩ := rel χ
  obtain ⟨h', hh', e₂⟩ := rel (F.f • F.xi a)
  have m : charVal t χ (closedPoint K) J ∈ H := by
    rw [e₁, ha, eq_mul_inv_of_mul_eq e₂.symm]
    exact H.mul_mem (H.mul_mem (img a) (H.inv_mem hh')) hh
  exact congrArg Units.val m

end GlobalTheory.Mum.ETors
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

theorem pull_lam_av {A : AbVar K} (c : Pic A.X.left) {Y Z : Over (Sp K)} (u : Z ⟶ Y) (x y : Y ⟶ A.X) :
    CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) := by
  simp only [AbVar.lam, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem pull_one_eq_zero {A : AbVar K} (c : Pic A.X.left) (Y : Over (Sp K)) :
    CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
  exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
    have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc

theorem exists_phi : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A',
    AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧
      (IsAmpleCls c → IsIsogeny φ) := by
  intro K _ A A' P hP hdim c
  set β : Pic (A.X ⊗ A.X).left := AbVar.lam c (fst A.X A.X) (snd A.X A.X) with hβ
  have hpull : ∀ {Y : Over (Sp K)} (x y : Y ⟶ A.X),
      CechPic.pull (lift x y).left β = AbVar.lam c x y := fun x y => by
    rw [hβ, pull_lam_av, lift_fst, lift_snd]
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ A.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β := by
    intro Y a a' t
    rw [hpull, hpull, hpull]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K A c Y a a' t
  have hnorm : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left β = 0 := by
    rw [hpull, AbVar.lam, _root_.mul_one, pull_one_eq_zero, sub_self, sub_zero]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' A P hP β hadd hnorm
  refine ⟨ψ, hψ, fun hc => ?_⟩
  have hfin : IsFinite ψ.hom.left := by
    refine (GlobalTheory.T.isFinite_iff_finite_ker' K A A' ψ).2 ?_
    have hF := GlobalTheory.T.finite_mumfordClass_eq_zero_ample K A c hc
    refine Finite.of_injective (β := {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K)))
      (snd A.X _ ≫ x) = 0}) (fun x => ⟨x.1, ?_⟩) ?_
    · have hx : x.1 ≫ ψ.hom = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, ptMap_apply] at this
        exact this
      rw [← hpull, hψ, AbDual.pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hx, MonObj.comp_one]
      exact AbDual.evc_one_right hP.isLB hP.zero _
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A A' ψ hdim.symm hfin⟩

end GlobalTheory.AV.AbVar
end
end
