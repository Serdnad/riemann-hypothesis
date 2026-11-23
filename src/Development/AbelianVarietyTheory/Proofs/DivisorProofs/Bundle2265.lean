module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Mathlib.Algebra.Category.ModuleCat.Free
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | exact GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.surjective_of_isFinite_of_dim_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem scheme_constantSection_add {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a + b) = constFn p U a + constFn p U b := by
  simp [constFn, map_add (f := _)]

theorem constFn_mul_on_open {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a * b) = constFn p U a * constFn p U b := by
  simp [constFn, map_mul]

theorem gammaSpecIso_appLE_of_eq_id_apply {R : Type} [CommRing R] (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (e : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ ⊤) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = r := by
  subst hf
  simp only [Scheme.Hom.appLE]
  erw [show (homOfLE e) = 𝟙 _ from Subsingleton.elim _ _]
  simp

theorem gammaSpecIso_appLE_section_constantSection_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (e : Sp R ⟶ X) (he : e ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ e ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r)) = r := by
  have hc := Scheme.Hom.appLE_comp_appLE e p ⊤ U ⊤ (fun _ _ => trivial) h
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ e.appLE U ⊤ h).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
    _ = _ := by rw [hc]
    _ = r := gammaSpecIso_appLE_of_eq_id_apply _ he _ r

end GlobalTheory.Heat

namespace GlobalTheory.Heat

theorem liftDer_isDerivation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens)
    (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  intro R _ G _ D W d hL hW
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  let ev : Γ(G.left, W) →+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (((η[G]).left.appLE W ⊤ hW).hom)
  have hev : ∀ r, ev (constFn G.hom W r) = r := fun r => gammaSpecIso_appLE_section_constantSection_eq G.hom _ he W hW r
  have hc : ∀ r, d W (constFn G.hom W r) = constFn G.hom W (D r) := hL.2 W le_rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have := congrArg ev (hc (a + b))
    rw [scheme_constantSection_add, hL.1.1 W le_rfl, hc, hc, map_add (f := _), hev, hev, hev] at this
    exact this.symm
  have hmul : ∀ a b, D (a * b) = a * D b + b * D a := by
    intro a b
    have := congrArg ev (hc (a * b))
    rw [constFn_mul_on_open, hL.1.2.1 W le_rfl, hc, hc, map_add (f := _), map_mul, map_mul, hev, hev, hev, hev, hev] at this
    exact this.symm
  let L : R →ₗ[ℤ] R := (AddMonoidHom.mk' D hadd).toIntLinearMap
  exact ⟨Derivation.mk' L (fun a b => by simpa [L, smul_eq_mul] using hmul a b), fun r => rfl⟩

end GlobalTheory.Heat
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem isInv_constFn (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by
  refine TopCat.Presheaf.section_ext G.left.sheaf O _ _ fun y hy => ?_
  let g : Sp (G.left.presheaf.stalk y) ⟶ G.left := G.left.fromSpecStalk y
  let φ : R →+* G.left.presheaf.stalk y := (Spec.preimage (g ≫ G.hom)).hom
  have hφ : g ≫ G.hom = spMap φ := (Spec.map_preimage (g ≫ G.hom)).symm
  have ht : ⊤ ≤ g ⁻¹ᵁ O := by
    intro z _
    have hz : g z ∈ Set.range g := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open O.isOpen hy
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := by
    intro A B C _ _ _ f f'
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let g' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap _ (DualNumber (G.left.presheaf.stalk y))) ≫ g) (by simp)
  have hdual : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
      rw [Category.assoc, Over.w (tv v)]
      simp only [Over.mk_hom, Category.comp_id]
      rw [← hcomp, hdual, hcomp, hφ])
  have key := hv.2 _ φ g (g' * v').left O (constFn G.hom O r) hφ ht ⟨g', v', rfl, rfl, rfl⟩
  have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
    by_cases hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
    · rw [GlobalTheory.Points.valR_constFn_of_over G.hom ((algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ)
        _ ?_ O hw r]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Over.w (g' * v'), hcomp]
        simp only [Over.mk_hom]
        rw [hφ]
    · simp [valR, dif_neg hw]
  rw [h0] at key
  exact ((GlobalTheory.FormalValue.valR_fromSpecStalk y O hy _).symm.trans key.symm).trans
    (map_zero (G.left.presheaf.germ O y hy).hom).symm

end GlobalTheory.Heat
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT pbT)
open GlobalTheory.LogKS (IsField)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m : G.left ⟶ X) {m₁ : G.left ⟶ X} {L : LB X} {dd : Fin n → Fld G.left} {D : R → R} (h₁ : Heat G m₁ L dd D)

def W (p : h₁.J × (Fin 2 → L.ι)) : G.left.Opens := h₁.W p.1 ⊓ LB.wchart L ![m, m₁] p.2

theorem heatGaugeCoverOpen_le_heatOperatorOpen (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ h₁.W p.1 := inf_le_left

theorem W_le_wchart (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ LB.wchart L ![m, m₁] p.2 := inf_le_right

theorem W_le_m (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m ⁻¹ᵁ L.U (p.2 0) :=
  (W_le_wchart m h₁ p).trans (LB.wchart_le L ![m, m₁] p.2 0)

theorem W_le_m₁ (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m₁ ⁻¹ᵁ (L.U (p.2 1) ⊓ L.U (h₁.j p.1)) :=
  fun _ hy => ⟨LB.wchart_le L ![m, m₁] p.2 1 hy.2, h₁.le p.1 hy.1⟩

variable (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

def gU (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p)ˣ :=
  res (W_le_wchart m h₁ p) (e.s p.2) * res (W_le_m₁ m h₁ p) (pullU m₁ _ (L.g (p.2 1) (h₁.j p.1)))

def gL (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  dd a (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gE (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  h₁.d p.1 (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gY (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e b p

def gD (p : h₁.J × (Fin 2 → L.ι)) : Fld G.left :=
  fun O f => h₁.d p.1 O f + ∑ a, rsT (gY m h₁ e a p) O * dd a O f

def gP (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p p.1) (W m h₁ p) - gE m h₁ e p -
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e a p * gL m h₁ e b p

def gP' (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p' p.1) (W m h₁ p) +
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * dd a (W m h₁ p) (gL m h₁ e b p) -
    ∑ a, constFn G.hom (W m h₁ p) (h₁.u a) * gL m h₁ e a p

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : Fld Z} (h : IsField W₀ d) (hle : W₁ ≤ W₀) :
    IsField W₁ d :=
  ⟨fun W hW => h.1 W (hW.trans hle), fun W hW => h.2.1 W (hW.trans hle),
    fun W W' hWW' hW => h.2.2 W W' hWW' (hW.trans hle)⟩


open GlobalTheory.KS in
theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (dd : Fin n → Fld G.left) (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (d : Fld G.left) {W₀ : G.left.Opens} (p p' : Γ(G.left, W₀)) (k : ℕ) {O O' : G.left.Opens}
    (hd : IsField O d) (hO : O ≤ W₀) (h : O' ≤ O) (f : Γ(G.left, O)) :
    rsT (op G dd Θ u d p p' k O f) O' = op G dd Θ u d p p' k O' (rsT f O') := by
  have hd' : ∀ g, resG G.left h (d O g) = d O' (resG G.left h g) :=
    fun g => (hd.2.2 O O' h le_rfl g).symm
  have hdd' : ∀ a g, resG G.left h (dd a O g) = dd a O' (resG G.left h g) :=
    fun a g => ((hdd a).2.2 O O' h le_top g).symm
  have hc : ∀ r, resG G.left h (constFn G.hom O r) = constFn G.hom O' r :=
    fun r => (rsT_of_le h _).symm.trans (rsT_constFn G.hom h r)
  have hp : ∀ q : Γ(G.left, W₀), resG G.left h (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h, rsT_rsT hO h]
  rw [rsT_of_le h, rsT_of_le h]

  simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem trans_factor {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : GlobalTheory.RayEv.Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) :
    ∃ τ : Q.P.A.left ⟶ Q.P.A.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left = Y.q.left ≫ τ := by
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  refine ⟨(𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)).left, ?_⟩
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc Y.q (toUnit _),
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg (fun f => f.left) e

end GlobalTheory.Heat.Gauge
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BertiniTop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem bertini : Quoted → Bertini := by
  intro hq F _ _ T hG hB δ f hf
  obtain ⟨-, hdeg, hdim⟩ :=
    GlobalTheory.ImageDegree.degree_image_eq_topSelf hq F T.toLinSys hG.alg.variety hG.alg.bpf hB
  have hprime : T.imageIdeal.IsPrime := HeightExists.isPrime_imageIdeal (S := T.toLinSys) hG.alg.variety
  have hhom : ∀ a ∈ T.imageIdeal, ∀ n : ℕ, homogeneousComponent n a ∈ T.imageIdeal := by
    intro a ha n
    have h := T.toLinSys.isHomogeneous_imageIdeal n ha
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin T.N) F) a n : MvPolynomial (Fin T.N) F) =
      homogeneousComponent n a from MvPolynomial.decomposition.decompose'_apply a n] at h
  have hδ : (δ : ℤ) = T.del := by
    rw [GlobalTheory.ChowDegree.degree_eq_hilbertDegree_of_isChowForm F T.D T.N δ T.imageIdeal f hf hprime hhom]
    exact hdeg
  refine ⟨hδ, ?_⟩
  obtain ⟨d₁, g₁, hg₁, hg₁I, hg₁v⟩ := GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary F T hG hB
  obtain ⟨d₂, g₂, hg₂, hg₂I, hg₂f⟩ := GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨Q₁, hQ₁, hQ₁v⟩ := GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone F T.D T.N (d₁ + d₂) T.imageIdeal (g₁ * g₂) hG.alg.variety.one_le hprime hhom
    hdim (hg₁.mul hg₂) fun h => (hprime.mem_or_mem h).elim hg₁I hg₂I
  obtain ⟨Q₂, hQ₂, -, hQ₂n⟩ :=
    GlobalTheory.PencilDisc.exists_poly_noSquare F T.D T.N δ f hf.isChowFormInt.pos hf.homog hf.irred
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun E _ _ s hs => ?_⟩
  have hs' : aeval (fun p : Fin T.D × Fin T.N => algebraMap E (AlgebraicClosure E) (s p.1 p.2)) (Q₁ * Q₂) ≠ 0 := by
    have h := MvPolynomial.aeval_algebraMap_apply (AlgebraicClosure E)
      (fun p : Fin T.D × Fin T.N => s p.1 p.2) (Q₁ * Q₂)
    exact fun h0 => hs ((map_eq_zero (algebraMap E (AlgebraicClosure E))).1 (h.symm.trans h0))
  rw [map_mul] at hs'
  have hns : NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) :=
    hQ₂n _ _ (right_ne_zero_of_mul hs')
  obtain ⟨hfin, hopen⟩ := GlobalTheory.T.linearSection_finite_inOpen_off_badForm F T hG δ f hf (g₁ * g₂)
    (fun K _ _ x hx => by rw [map_mul, hg₁v K x hx, zero_mul])
    (fun K _ _ y => (hg₂f K y).subset fun x hx => ⟨right_ne_zero_of_mul (by simpa only [map_mul] using hx.1), hx.2⟩)
    E s hns.1 fun x hx h0 => by
      refine left_ne_zero_of_mul hs' (hQ₁v (AlgebraicClosure E) (fun i j => algebraMap E _ (s i j)) _
        (hG.alg.bpf.coords_ne_zero _) (fun a ha => ?_) h0 ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx))
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 ha
      rwa [LinSys.baseHom_ptOver] at this
  exact GlobalTheory.T.linearSection_etale_of_squarefree_chowForm F T hG δ f hf hδ E s hfin hopen hns

end GlobalTheory.BertiniTop
end

section

open GlobalTheory.LKTrip

theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopFrameEt

open GlobalTheory.TopForm

theorem appLE_comp_algX' {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (q : Y ⟶ X)
    {U : X.Opens} {W : Y.Opens} (h : W ≤ q ⁻¹ᵁ U) :
    (q.appLE U W h).hom.comp (algX p U) = algX (q ≫ p) W := by
  have e := Scheme.Hom.appLE_comp_appLE q p ⊤ U W le_top h
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem exists_basis_of_exact {R M₁ M₂ M₃ ι ι' : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f) (hex : Function.Exact f g)
    (v : Module.Basis ι R M₁) (w : Module.Basis ι' R M₃) (u : ι' → M₂) (hu : ∀ a, g (u a) = w a) :
    ∃ b : Module.Basis (ι ⊕ ι') R M₂, ∀ j, b j = Sum.elim (fun i ↦ f (v i)) u j := by
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (by ext x; exact hex.apply_apply_eq_zero x)
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
  have hm : Mono S.f := (ModuleCat.mono_iff_injective _).2 hf
  let u' : ι ⊕ ι' → M₂ := Sum.elim (fun i ↦ f (v i)) u
  have hw : (S.g ∘ u' ∘ Sum.inr) = w := funext fun a ↦ hu a
  have hli : LinearIndependent R u' := by
    refine ModuleCat.linearIndependent_leftExact (S := S) (v := v) hS v.linearIndependent ?_ hm ?_
    · rw [hw]; exact w.linearIndependent
    · rfl
  have hsp : ⊤ ≤ Submodule.span R (Set.range u') := by
    refine ModuleCat.span_exact (S := S) (v := v) hS rfl (by rw [v.span_eq]) ?_
    rw [hw, w.span_eq]
  exact ⟨Module.Basis.mk hli hsp, fun j ↦ by simp [u']⟩

theorem isFrame_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  intro k _ X Y p q p' hp m D _ ι o U U' hU' hU W W' hW' hW hW'a hWU hW'U' N hN x hx
  subst hp
  have hU'a : IsAffineOpen U' := hx.affine
  have hC := GlobalTheory.T.etale_mvPolynomial_eval2Hom_restrict_smaller_affines X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  obtain ⟨bR, hbR⟩ := GlobalTheory.T.exists_kaehlerBasis_differentials_of_topFormFrame k X p m ‹_› U' _ hx
  haveI : Finite ι := Finite.of_injective (fun a ↦ o.symm (Sum.inr a))
    (fun a b h ↦ Sum.inr_injective (o.symm.injective h))
  letI : Algebra k Γ(X, U') := (algX p U').toAlgebra
  letI : Algebra k Γ(Y, W') := (algX (q ≫ p) W').toAlgebra
  letI : Algebra Γ(X, U') Γ(Y, W') := (q.appLE U' W' hW'U').hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U') Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq' (appLE_comp_algX' p q hW'U').symm
  let φ := MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))
  letI : Algebra (MvPolynomial ι Γ(X, U')) Γ(Y, W') := φ.toAlgebra
  haveI : IsScalarTower Γ(X, U') (MvPolynomial ι Γ(X, U')) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (MvPolynomial.C r)
      simp [φ]; rfl
  haveI : Algebra.Etale (MvPolynomial ι Γ(X, U')) Γ(Y, W') := hC
  obtain ⟨⟨bT, hbT⟩, hsm⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale Γ(X, U') Γ(Y, W') ι
  haveI := hsm
  haveI : Subsingleton (Algebra.H1Cotangent Γ(X, U') Γ(Y, W')) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W')) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k Γ(X, U') Γ(Y, W') y).1 hy
    rw [Subsingleton.elim z 0, map_zero]
  obtain ⟨b, hb⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W'))
    (KaehlerDifferential.map k Γ(X, U') Γ(Y, W') Γ(Y, W')) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k Γ(X, U') Γ(Y, W'))
    (bR.baseChange Γ(Y, W')) bT (fun a ↦ KaehlerDifferential.D k Γ(Y, W') (resG Y hW' (N a)))
    (fun a ↦ by rw [hbT, KaehlerDifferential.map_D]; simp [φ, RingHom.algebraMap_toAlgebra])
  refine ⟨hW'a, isFreeGen_dForm _ (b.reindex o.symm) fun a ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
  rcases o a with i | i
  · simp only [Sum.elim_inl, Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul,
      one_smul, hbR, dFun, KaehlerDifferential.map_D]
    refine congrArg (KaehlerDifferential.D k Γ(Y, W')) ?_
    rw [RingHom.algebraMap_toAlgebra, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.resG_appLE]
  · rfl

end GlobalTheory.TopFrameEt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRealForm

theorem vacuum_real_law : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D) (δ : ℂ), GlobalTheory.FockCompare.Chart W.θ σ → Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pS (.top t j)).rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D (G.pT (.top t j)).rank), ∀ Y, Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) x (GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ) Y = GlobalTheory.VacRealForm.thY σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f δ Y := by
  intro D T L sc G W U N σ δ hσ hcrv hδ t j hj f hf x hx Y
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.T.torusLattice_standard_points_scaled_embedding δ x hx
  have hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top j)).1 * (G.V (.top j)).gram * (N.fr (.top j)).1 = 1 :=
    N.fr_on (.top j) (show j ≤ D.R.m by omega)
  have hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (N.fr (.top (j + 1))).1 * (G.V (.top (j + 1))).gram *
      (N.fr (.top (j + 1))).1 = 1 := N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)
  have hlat := GlobalTheory.T.orthonormalFrame_finitePart_mem_completedLattice (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS M hM
  obtain ⟨k, hk, heig⟩ := GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (colLat (N.fr (.top j))) (colLat (N.fr (.top (j + 1))))
    hf.1 (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hS) (GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame _ _ hT) f hf.2.lat _ hlat
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hσ hf.1 hf.2.theta _ heig
  rw [GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing, neg_zero, AddChar.map_zero_eq_one, one_mul] at hlaw
  have hU := GlobalTheory.T.torusTranslate_thetaCoordinate_of_realPart_law σ (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M f _ hlaw Y
  have hal := GlobalTheory.T.torusSemicharacter_eq_neg_one_pow_traceExponent (G.V (.top j)) (G.V (.top (j + 1))) (N.fr (.top j)) (N.fr (.top (j + 1))) hS hT δ hδ M k hk
  show Formalism.MainNotions.TaylorLogMetric.al D _ _ * Formalism.MainNotions.TaylorLogMetric.U D _ _ (thY σ (G.V (.top j)) (G.V (.top (j + 1))) (fun τ => (N.fr (.top j)).1.map (tauE D τ))
    (fun τ => (N.fr (.top (j + 1))).1.map (tauE D τ)) f δ) Y = _
  rw [hU, ← mul_assoc, hal, one_mul]
  rfl

end GlobalTheory.VacRealForm
end
