module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegWLocalFunctionsThetaPureTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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
open GlobalTheory.CechKS

theorem _root_.GlobalTheory.T.isDeformationChartPoint_spec_map : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  first | exact @GlobalTheory.CechKS.isChartPt_spMap | exact GlobalTheory.CechKS.isChartPt_spMap | (intros; apply GlobalTheory.CechKS.isChartPt_spMap <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_smul_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_smul | exact GlobalTheory.CoordsOrigin.tanDer_smul | (intros; apply GlobalTheory.CoordsOrigin.tanDer_smul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.exists_tangentVector_of_originDerivation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (constO G r) = 0) → ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  first | exact @GlobalTheory.CoordsOrigin.exists_tan_of_derivation | exact GlobalTheory.CoordsOrigin.exists_tan_of_derivation | (intros; apply GlobalTheory.CoordsOrigin.exists_tan_of_derivation <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_add | exact GlobalTheory.CoordsOrigin.tanDer_add | (intros; apply GlobalTheory.CoordsOrigin.tanDer_add <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

theorem _root_.GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G), (∀ f, tanDer G u f = tanDer G v f) → u = v := by
  first | exact @GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | exact GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | (intros; apply GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left) (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧ ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  first | exact @GlobalTheory.InvForm.exists_transl_val | exact GlobalTheory.InvForm.exists_transl_val | (intros; apply GlobalTheory.InvForm.exists_transl_val <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  first | exact @GlobalTheory.InvFormProj.finite_projective | exact GlobalTheory.InvFormProj.finite_projective | (intros; apply GlobalTheory.InvFormProj.finite_projective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), m.Coprime p → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.kernel_descent | exact GlobalTheory.UPel.HT.Hecke.kernel_descent | (intros; apply GlobalTheory.UPel.HT.Hecke.kernel_descent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.biextension_trivial_of_translate_difference_trivial : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.PicBilin.triv_pow_of_translDiff) | (exact GlobalTheory.PicBilin.triv_pow_of_translDiff) | (intros; apply GlobalTheory.PicBilin.triv_pow_of_translDiff  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

abbrev R2 (S : Type) [CommRing S] := DualNumber (DualNumber S)

def mergeHom (S : Type) [CommRing S] : R2 S →+* DualNumber S where
  toFun z := z.fst + TrivSqZeroExt.inr z.snd.fst
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

def dmap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (φ z.fst) + TrivSqZeroExt.inr (φ z.snd)
  map_one' := by ext <;> simp
  map_mul' := by
    intro x y
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp <;> ring

@[simp] theorem dmap_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).fst = φ z.fst := by simp [dmap]

@[simp] theorem dmap_snd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z : DualNumber A) :
    (dmap φ z).snd = φ z.snd := by simp [dmap]

@[simp] theorem mergeHom_fst (z : R2 S) : (mergeHom S z).fst = z.fst.fst := by simp [mergeHom]

@[simp] theorem mergeHom_snd (z : R2 S) : (mergeHom S z).snd = z.fst.snd + z.snd.fst := by simp [mergeHom]

def ovHom {X : Scheme.{0}} (x : Sp S ⟶ X) {A B : Type} [CommRing A] [CommRing B] (a : S →+* A) (b : S →+* B)
    (φ : A →+* B) (h : φ.comp a = b) : Over.mk (spMap b ≫ x) ⟶ Over.mk (spMap a ≫ x) :=
  Over.homMk (spMap φ) (by
    change spMap φ ≫ spMap a ≫ x = spMap b ≫ x
    rw [← Category.assoc, ← spMap_comp_eq, h])

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (ψ : B →+* A)
    (h : φ.comp ψ = RingHom.id B) : spMap φ ≫ spMap ψ = 𝟙 _ := by
  rw [← spMap_comp_eq, h]
  show Spec.map (CommRingCat.ofHom (RingHom.id B)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

variable {S : Type} [CommRing S]

theorem snd_valR_mul_mul {X : Scheme.{0}} {G : Over X} [GrpObj G] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G) (hg' : g'.left = spMap (algebraMap S (DualNumber S)) ≫ g)
    (p q : tEpsG (g ≫ G.hom) ⟶ G) (hp : redOver (g ≫ G.hom) ≫ p = 1) (hq : redOver (g ≫ G.hom) ≫ q = 1)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    (valR (g' * (p * q)).left O f).snd = (valR (g' * p).left O f).snd + (valR (g' * q).left O f).snd := by
  let x := g ≫ G.hom
  let α := algebraMap S (DualNumber S)
  let i₁ : DualNumber S →+* R2 S := TrivSqZeroExt.inlHom (DualNumber S) (DualNumber S)
  let i₂ : DualNumber S →+* R2 S := dmap α
  let j : S →+* R2 S := i₁.comp α
  let fs : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom
  let r₁ : R2 S →+* DualNumber S := (TrivSqZeroExt.fstHom (DualNumber S) (DualNumber S) (DualNumber S)).toRingHom
  let r₂ : R2 S →+* DualNumber S := dmap fs
  have hi₂ : i₂.comp α = j := by ext s <;> simp [i₂, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : (mergeHom S).comp j = α := by ext s <;> simp [i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₁ : r₁.comp j = α := by ext s <;> simp [r₁, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  have hr₂ : r₂.comp j = α := by ext s <;> simp [r₂, fs, i₁, j, α, TrivSqZeroExt.algebraMap_eq_inl]
  let K₁ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₁ rfl
  let K₂ : Over.mk (spMap j ≫ x) ⟶ tEpsG x := ovHom x α j i₂ hi₂
  let M : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α (mergeHom S) hm
  let R₁ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₁ hr₁
  let R₂ : tEpsG x ⟶ Over.mk (spMap j ≫ x) := ovHom x j α r₂ hr₂
  let C : Over.mk (spMap j ≫ x) ⟶ G := Over.homMk (spMap j ≫ g) (Category.assoc _ _ _)
  let φ : tEpsG x ⟶ Over.mk x := Over.homMk (spMap α) rfl
  let P : Over.mk (spMap j ≫ x) ⟶ G := C * ((K₁ ≫ p) * (K₂ ≫ q))
  have hC : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α), ovHom x j α ρ h ≫ C = g' := fun ρ h =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap j ≫ g = g'.left
      rw [hg', ← Category.assoc, ← spMap_comp_eq, h])
  have hid : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = RingHom.id _ → ovHom x j α ρ h ≫ ovHom x α j κ h' = 𝟙 _ := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = 𝟙 _
      exact spMap_comp_eq_id ρ κ e)
  have hred : ∀ (ρ : R2 S →+* DualNumber S) (h : ρ.comp j = α) (κ : DualNumber S →+* R2 S) (h' : κ.comp α = j),
      ρ.comp κ = α.comp fs → ovHom x j α ρ h ≫ ovHom x α j κ h' = φ ≫ redOver x := fun ρ h κ h' e =>
    Over.OverMorphism.ext (by
      change spMap ρ ≫ spMap κ = spMap α ≫ spMap fs
      rw [← spMap_comp_eq, ← spMap_comp_eq, e])
  have hMK₁ : M ≫ K₁ = 𝟙 _ := hid _ hm _ rfl (by ext s <;> simp [i₁])
  have hMK₂ : M ≫ K₂ = 𝟙 _ := hid _ hm _ hi₂ (by ext s <;> simp [i₂, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₁K₁ : R₁ ≫ K₁ = 𝟙 _ := hid _ hr₁ _ rfl (by ext s <;> simp [r₁, i₁])
  have hR₁K₂ : R₁ ≫ K₂ = φ ≫ redOver x :=
    hred _ hr₁ _ hi₂ (by ext s <;> simp [r₁, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₁ : R₂ ≫ K₁ = φ ≫ redOver x :=
    hred _ hr₂ _ rfl (by ext s <;> simp [r₂, i₁, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have hR₂K₂ : R₂ ≫ K₂ = 𝟙 _ := hid _ hr₂ _ hi₂ (by ext s <;> simp [r₂, i₂, fs, α, TrivSqZeroExt.algebraMap_eq_inl])
  have eM : M ≫ P = g' * (p * q) := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc M K₁, ← Category.assoc M K₂, hMK₁, hMK₂, Category.id_comp, Category.id_comp]
  have e1 : R₁ ≫ P = g' * p := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₁ K₁, ← Category.assoc R₁ K₂, hR₁K₁, hR₁K₂, Category.id_comp,
      Category.assoc, hq, comp_one, _root_.mul_one]
  have e2 : R₂ ≫ P = g' * q := by
    simp only [P, comp_mul]
    rw [hC, ← Category.assoc R₂ K₁, ← Category.assoc R₂ K₂, hR₂K₁, hR₂K₂, Category.id_comp,
      Category.assoc, hp, comp_one, _root_.one_mul]
  have hgp : spMap fs ≫ (g' * p).left = g := by
    change (redOver x ≫ (g' * p)).left = g
    rw [comp_mul, hp, _root_.mul_one]
    change spMap fs ≫ g'.left = g
    rw [hg', ← Category.assoc, spMap_fst_algebraMap, Category.id_comp]
  have hP1 : spMap r₁ ≫ P.left = (g' * p).left := by rw [← e1]; rfl
  have hPO : ⊤ ≤ P.left ⁻¹ᵁ O := GlobalTheory.CechKS.le_preimage_of_red hP1 (GlobalTheory.CechKS.le_preimage_of_red hgp hO)
  rw [← eM, ← e1, ← e2]
  change (valR (spMap (mergeHom S) ≫ P.left) O f).snd =
    (valR (spMap r₁ ≫ P.left) O f).snd + (valR (spMap r₂ ≫ P.left) O f).snd
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f, GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f,
    GlobalTheory.Points.valR_spMap_comp _ _ _ hPO f]
  simp [r₁, r₂, fs]

end GlobalTheory.EpsAdd

namespace GlobalTheory.EpsAdd

open GlobalTheory.VertSpanZero

theorem snd_valR_mul_prod : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left)
    (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g →
    ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)),
    (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) →
    ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O),
    (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := by
  intro X G _ S _ g g' hg' n
  induction n with
  | zero =>
    intro u _ O hO f
    rw [List.ofFn_zero, List.prod_nil, _root_.mul_one, hg', GlobalTheory.Points.valR_spMap_comp _ _ _ hO f]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  | succ n ih =>
    intro u hu O hO f
    have hu' : ∀ a, redOver (g ≫ G.hom) ≫ u a = 1 := fun a => Over.OverMorphism.ext (hu a)
    have hrest : redOver (g ≫ G.hom) ≫ (List.ofFn fun i : Fin n => u i.succ).prod = 1 := by
      refine redOver_comp_prod _ _ fun w hw => ?_
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ w).1 hw
      exact hu' _
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      snd_valR_mul_mul g g' hg' _ _ (hu' 0) hrest O hO f, ih (fun i => u i.succ) (fun a => hu _) O hO f]

end GlobalTheory.EpsAdd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.negW_local_functions_theta_pure_tensor : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ (ρ : RealMatch W) f₀,
      GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (_root_.GlobalTheory.TopFlip.ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) (_root_.GlobalTheory.TopFlip.vacA ρ i j) →
      ∀ ι : ∀ w, ToA G t i j w, (∀ w ∈ locPl G t, _root_.GlobalTheory.TopFlip.IsLinModelA W B t e Γ w (ι w)) →
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ F, _root_.GlobalTheory.TopFlip.IsLinA B t i j ρ ε Ξ F →
      ∀ φ, IsFinPart Γ.M X.T φ → (∀ w ∈ locPl G t, ι w (φ (w.under (𝓞 D.host.F))) = Ξ w) →
        GlobalTheory.SquareAgree.IsDatum Γ.M W.ψ (_root_.GlobalTheory.TopFlip.ptA e) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0) • f₀) φ) F := by
  exact @GlobalTheory.TopFlip.LinGlob.isDatum_linA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Transport

theorem l2A_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilL2Words.l2A D.host.F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A D.host.F μ Φ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  refine GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn D.host.F κ om ?_
    (GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom)
  rintro ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB a b
  exact (hom a b g h hh hg Φ hΦ).1

end GlobalTheory.WeilL2Transport

end
end
