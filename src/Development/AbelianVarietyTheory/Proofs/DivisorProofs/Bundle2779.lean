module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RosatiSymmetry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem padd_comm' {T : Over S} (x y : T ⟶ A) : padd A x y = padd A y x := by
  show x * y = y * x
  exact mul_comm x y

abbrev sw : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)

theorem sw_padd (x y : A ⊗ A ⟶ A) : sw A ≫ padd A x y = padd A (sw A ≫ x) (sw A ≫ y) := by
  simp only [padd, comp_lift_assoc]

theorem formEq_sw (f g : A ⟶ A) (Y : Scheme.{0}) (p : Y ⟶ (A ⊗ A).left) :
    FormEq (fun k => p ≫ (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k)
      (fun k => p ≫ rosatiφ A f g k) rosatiε := by
  intro U _ h
  have e0 : (sw A).left ≫ (padd A (fst A A ≫ g) (snd A A)).left = (padd A (fst A A) (snd A A ≫ g)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst_assoc, lift_snd]
  have e1 : (sw A).left ≫ (fst A A ≫ g).left = (snd A A ≫ g).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e2 : (sw A).left ≫ (snd A A).left = (fst A A).left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : (sw A).left ≫ (padd A (fst A A) (snd A A ≫ f)).left = (padd A (fst A A ≫ f) (snd A A)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst, lift_snd_assoc]
  have e4 : (sw A).left ≫ (fst A A).left = (snd A A).left := by
    rw [← Over.comp_left, lift_fst]
  have e5 : (sw A).left ≫ (snd A A ≫ f).left = (fst A A ≫ f).left := by
    rw [← Over.comp_left, lift_snd_assoc]
  simp only [Fin.prod_univ_six, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.head_cons, e0, e1, e2, e3, e4, e5]
  simp only [neg_neg, zpow_neg, zpow_one]
  ac_rfl

theorem formEq_sw' (f g : A ⟶ A) :
    FormEq (fun k => (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k) (rosatiφ A f g) rosatiε := by
  simpa only [Category.id_comp] using formEq_sw A f g _ (𝟙 _)

theorem rosatiAdj_symm (L : LB A.left) (hL : L.IsLB) (f g : A ⟶ A) (h : RosatiAdj A L f g) : RosatiAdj A L g f := by
  intro s
  obtain ⟨U, hs, t, ht⟩ := h s
  refine ⟨U, hs, ?_⟩
  have hW : (A ⊗ A).hom ⁻¹ᵁ U ≤ (sw A).left ⁻¹ᵁ ((A ⊗ A).hom ⁻¹ᵁ U) := by
    intro x hx
    show ((sw A).left ≫ (A ⊗ A).hom) x ∈ U
    rw [Over.w]; exact hx
  let σ := (sw A).left.resLE ((A ⊗ A).hom ⁻¹ᵁ U) ((A ⊗ A).hom ⁻¹ᵁ U) hW
  have hσ : σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left := Scheme.Hom.resLE_comp_ι _ _
  have hF : FormEq (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) (fun k => - rosatiε k)
      (fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A g f k) rosatiε := by
    have e : (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) =
        fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left ≫ rosatiφ A f g k := by
      funext k; rw [← Category.assoc, hσ, Category.assoc]
    rw [e]; exact formEq_sw A g f _ _
  obtain ⟨t', ht', -⟩ := exists_gen hL hF (LB.invGen L _ _ (LB.pullGen L _ _ t σ))
    (DVR.invGen_isGen L _ _ _ (DVR.pullGen_isGen L _ _ t ht σ))
  exact ⟨t', ht'⟩

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum.RosatiSymmetry
variable {R : Type} [CommRing R] [IsDomain R]

theorem val_tau_symm (D : DegPre R) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (r : Z ⟶ (TK R).left) (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  simp only [DegPre.tau, val_mul hJ, val_inv]
  have e : val (D.psi (a + b)) r z J = val (D.psi (b + a)) r z J := by rw [add_comm]
  rw [e, mul_right_comm (val (D.psi (b + a)) r z J)]

theorem tauBal_symm (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) (H : D.TauBal f g a a') :
    D.TauBal g f a' a := by
  intro u' hu' hn y y'
  have hL := D.P.isLB
  obtain ⟨u, hu, hv⟩ := exists_gen hL (formEq_sw' D.P.A f g)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u' (sw D.P.A).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u' hu' _))
  have hz : zero2 D.P.A ≫ (sw D.P.A).left = zero2 D.P.A := by
    rw [zero2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hp : D.pt2 y' y ≫ (sw D.P.A).left = D.pt2 y y' := by
    rw [DegPre.pt2, DegPre.pt2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hnu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) := by
    refine corr_of_val hL fun z J hJ => ?_
    have h1 := val_corr hJ hn (𝟙 _)
    rw [val_pull hJ, val_one] at h1
    rw [val_pull hJ, val_one, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hz, h1, inv_one]
  have H' := H u hu hnu y' y
  refine corr_of_val hL fun z J hJ => ?_
  have h2 := val_corr hJ H' (𝟙 _)
  rw [val_mul hJ, val_pull hJ, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hp] at h2
  rw [val_mul hJ, val_pull hJ, val_tau_symm D hJ _ (a' y) y', ← h2, val_tau_symm D hJ _ (a y') y]
  group

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum

theorem endData_symm_and_ofOAct : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    (∀ (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X), EndData D a a' h h' → EndData D a' a h' h) ∧
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (x : O),
      EndData D (o.onB.act x) (o.onB.act (star x)) (DistribSMul.toAddMonoidHom D.X x)
        (DistribSMul.toAddMonoidHom D.X (star x)) := by
  intro R _ _ D
  refine ⟨fun a a' h h' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h1, RosatiSymmetry.rosatiAdj_symm D.P.A D.P.L D.P.isLB a a' h3,
    h5, h4, RosatiSymmetry.tauBal_symm D a a' h h' h6⟩, fun O _ _ _ o x => ?_⟩
  exact ⟨o.onB.hom x, o.onB.hom (star x), o.onB.rosati x, fun y => o.c_lin x y, fun y => o.c_lin (star x) y,
    o.tau_bal x⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def transl {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : G ⟶ G :=
  𝟙 G * (Over.homMk G.hom (by simp) ≫ y)

def Near.chart {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : Option (Fin n) → (pullback N.U.hom π ⟶ G.left)
  | none => N.u
  | some k => N.u ≫ (transl (x k)⁻¹).left

theorem Near.chart_some {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) (k : Fin n) :
    N.chart x (some k) = N.u ≫ (transl (x k)⁻¹).left := rfl

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def UT (N : Near π G) : Over (pullback π π) := Over.mk (pullback.snd N.U.hom (pullback.fst π π ≫ π))

def toS (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback N.U.hom π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, hp]; exact pullback.condition)

def embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback G.hom p :=
  pullback.lift (toS N p hp ≫ N.u) (pullback.snd _ _) (by
    rw [Category.assoc, N.u_over, toS, pullback.lift_snd])

def emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⟶ (Over.pullback p).obj G :=
  Over.homMk (embL N p hp) (pullback.lift_snd _ _ _)

def sum [GrpObj G] (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⊗ UT N ⟶ (Over.pullback p).obj G :=
  (fst (UT N) (UT N) ≫ emb N p hp) * (snd (UT N) (UT N) ≫ emb N p hp)

end GlobalTheory.Mum.Desc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dense_of_closedFibre_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G],
    IsSemiAbelian G → ∀ O : G.left.Opens, (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → Dense (O : Set G.left) := by
  intro R _ _ _ G _ hG O hO
  haveI := hG.smooth
  haveI := hG.geomConnected
  let g₀ : G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left (closedPoint R)
  have hg₀ : G.hom g₀ = closedPoint R := by
    have := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
    change ((1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom) (closedPoint R) = closedPoint R
    rw [this]; rfl
  have : IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain R G inferInstance inferInstance ⟨g₀⟩
  exact O.isOpen.dense ⟨g₀, hO g₀ hg₀⟩

theorem spMap_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) : spMap ρ (closedPoint R') = closedPoint R := by
  algebraize [ρ]
  have : Algebra.IsIntegral R R' := ⟨fun x => hf.to_isIntegral x⟩
  apply PrimeSpectrum.ext
  show Ideal.comap ρ (maximalIdeal R') = maximalIdeal R
  have : (Ideal.comap (algebraMap R R') (maximalIdeal R')).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R')
  exact IsLocalRing.eq_maximalIdeal this

theorem comp_eq_of_near {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R') (hf : ρ.Finite) (G' : Over (Sp R')) [GrpObj G'] (hG' : IsSemiAbelian G') (N : Near (spMap ρ) G')
    (G : Over (Sp R)) [GrpObj G] (hG : IsSeparated G.hom) (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ)
    (i : N.U ⟶ G) (hu : N.u ≫ β = pullback.fst _ _ ≫ i.left) (σ : Gal ρ) (g : G'.left ⟶ G'.left)
    (hg : g ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ))
    (hinv : ∀ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x →
      N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ g)) : g ≫ β = β := by
  haveI := hG'.smooth
  haveI := N.isOpen
  have hred : IsReduced G'.left := GlobalTheory.isReduced_of_smooth_of_isReduced G'.hom
  have hd := dense_of_closedFibre_sub R' G' hG' N.u.opensRange (fun x hx => by
    obtain ⟨y, hy⟩ := N.all x (by rw [hx]; exact spMap_closedPoint_of_finite ρ hf)
    exact ⟨y, hy⟩)
  haveI : IsDominant N.u := ⟨by simpa [DenseRange] using hd⟩
  have hσ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact σ.2 r
  refine ext_of_isDominant_of_isSeparated G.hom ?_ N.u ?_
  · rw [Category.assoc, hβ, ← Category.assoc, hg, Category.assoc, hσ]
  · obtain ⟨x₁, h1, -, h3⟩ := hinv _ (pullback.snd _ _) (pullback.fst _ _) N.u ⟨𝟙 _, by simp, by simp, by simp⟩
    rw [← Category.assoc, ← h3, Category.assoc, hu, ← Category.assoc, h1]

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem hom_ext_of_cart {A : Over S} {A₁ : Over S'} [GrpObj A] [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A f φ) {T : Over S'} {u v : T ⟶ A₁} (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w u, Over.w v]))

theorem exists_baseChange {A B : Over S} {A₁ B₁ : Over S'} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
    {φ : A₁.left ⟶ A.left} {χ : B₁.left ⟶ B.left} (hA : IsGrpPullback A₁ A f φ) (hB : IsGrpPullback B₁ B f χ)
    (ψ : A ⟶ B) : ∃ ψ₁ : A₁ ⟶ B₁, ψ₁.left ≫ χ = φ ≫ ψ.left :=
  ⟨Over.homMk (hB.1.lift (φ ≫ ψ.left) A₁.hom (by rw [Category.assoc, Over.w ψ, hA.1.w]))
    (hB.1.lift_snd _ _ _), hB.1.lift_fst _ _ _⟩

theorem grpSchemeSquareProductMap_comp_fst {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    Hecke.sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' s s' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hm, hact, heta, ⟨hP⟩, ψ', hm', h₁, h₂⟩ := hψ
  obtain ⟨ψ₁, sq⟩ := exists_baseChange m.cart m'.cart ψ
  obtain ⟨ψ₁', sq'⟩ := exists_baseChange m'.cart m.cart ψ'
  haveI := hm
  haveI := hm'
  have hm₁ : IsMonHom ψ₁ := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m.cart m'.cart ψ ψ₁ sq
  have hm₁' : IsMonHom ψ₁' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback m'.cart m.cart ψ' ψ₁' sq'
  have hsq2 : Hecke.sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ Hecke.sq2 ψ := by
    apply Over.tensorObj_ext
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (fst o'.A o'.A).left = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, m.sq.1, Category.assoc]
      exact l.trans r.symm
    · change (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left
      have l : (Hecke.sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, sq]
      have r : (m.φ₂ ≫ Hecke.sq2 ψ) ≫ (snd o'.A o'.A).left = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
        rw [Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, m.sq.2, Category.assoc]
      exact l.trans r.symm
  refine ⟨ψ₁, ⟨hk, hm₁, fun a => ?_, fun x => ?_, ⟨?_⟩, ψ₁', hm₁', ?_, ?_⟩, sq.symm⟩
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.act.act a ≫ ψ₁).left ≫ m'.φ = m.φ ≫ (o.act.act a ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.act, Category.assoc]
    have e2 : (ψ₁ ≫ o₁'.act.act a).left ≫ m'.φ = m.φ ≫ (ψ ≫ o'.act.act a).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, sq, Category.assoc]
    rw [e1, e2, hact a]
  · apply hom_ext_of_cart m'.cart
    have e1 : (o₁.eta x ≫ ψ₁).left ≫ m'.φ = f ≫ (o.eta x ≫ ψ).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, sq, ← Category.assoc, m.eta, Category.assoc]
    rw [e1, m'.eta, heta x]
  · have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hL₁ (pull_isLB o₁'.isLB _)).1 ?_
    have e₁ := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    have e₂ := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
    have e₃ := (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB o'.isLB (Hecke.sq2 ψ))).2 hP
    rw [GlobalTheory.BirigidPow.cls_lbPow o.isLB, GlobalTheory.CechPic.cls_pull o'.isLB] at e₃
    rw [GlobalTheory.CechPic.cls_pull o.isLB] at e₁
    rw [GlobalTheory.CechPic.cls_pull o'.isLB] at e₂
    rw [GlobalTheory.BirigidPow.cls_lbPow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, e₂, ← GlobalTheory.CechPic.pull_comp, hsq2,
      GlobalTheory.CechPic.pull_comp, ← e₃, map_nsmul, ← e₁]
  · apply hom_ext_of_cart m.cart
    rw [ESDual.pow_left_comm m.cart c, Over.comp_left, Category.assoc, sq', ← Category.assoc, sq, Category.assoc,
      ← Over.comp_left, h₁]
  · apply hom_ext_of_cart m'.cart
    rw [ESDual.pow_left_comm m'.cart c, Over.comp_left, Category.assoc, sq, ← Category.assoc, sq', Category.assoc,
      ← Over.comp_left, h₂]

end GlobalTheory.UPel.HT.ESPull
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  first | exact @GlobalTheory.FormalAlg.LevSurj.ev_surjective | exact GlobalTheory.FormalAlg.LevSurj.ev_surjective | (intros; apply GlobalTheory.FormalAlg.LevSurj.ev_surjective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_projective_relations : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | exact GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | (intros; apply GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumTerm

variable {X Y Z : Scheme.{0}}

theorem scal_spec {A B : Type} [CommRing A] [CommRing B] (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ Spec.map (CommRingCat.ofHom φ)) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem gs_scal {A : Type} [CommRing A] (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem exists_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval t r z J = gs r z ⊤ a * sval s r z J := by
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f i, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, s.compat i j, mul_left_comm]
    congr 2
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · have hm := hJ.mem φ r
    exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem exists_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  intro R _ _ _ D a h h' N s₀ ν u₀ hu₀ ρ H
  obtain ⟨p, hp⟩ := exists_sec D.toPre.P.isLB (φ' := tφ D.toPre a (shift h h' N (-1) ν)) (ε' := tε N (-1))
    (fun U _ g => by
      simp only [Fintype.prod_sum_type, dε, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec s₀ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left u₀ hu₀)
  obtain ⟨t, ht⟩ := exists_smul (scal D.toPre.P.A.hom ρ) p
  refine ⟨t, fun u hu Z x z J hJ => ?_, fun e he Z x z J hJ => ?_⟩
  · have e₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left =
        (DegPre.trF D.toPre (FractionRing R) ν).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      simp only [DegPre.trF, padd, lift_snd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have e₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
          (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
      have j : jFK (R := R) (FractionRing R) = 𝟙 _ := by
        simp [jFK]
      rw [Over.w]
      refine (Over.w (fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_
      congr 1
      show jFK (R := R) (FractionRing R) ≫ jK R = jK R
      rw [j, Category.id_comp]
    rw [ht _ _ z J hJ, hp _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, H u hu Z x z J hJ, Category.assoc, e₁,
      scal_spec, gs_scal, gs_scal, Category.assoc, e₂, mul_left_comm]
  · rw [ht _ _ z J hJ, gs_scal, Category.assoc, pullback.condition, ← gs_scal, ← scal_spec,
      Ideal.Quotient.eq_zero_iff_mem.2 he]
    have : scal (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (0 : R ⧸ maximalIdeal R ^ (e + 1)) = 0 := by
      simp only [scal, map_zero]
    exact (congrArg (· * _) ((congrArg (gs x z ⊤) this).trans (DVR.gs_zero x z ⊤ trivial))).trans (zero_mul _)

end GlobalTheory.MumTerm
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  first | exact @GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | exact GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div | (intros; apply GlobalTheory.Poinc.mem_map_idealSheaf_of_forall_div <;> assumption)
end
