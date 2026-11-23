module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | exact GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | (intros; apply GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap <;> assumption)
end

section

open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem _root_.GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K),
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.FibreMulK

private theorem ev_nsmul' {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n j : ℕ) (y : D.La) :
    I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, _root_.pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, _root_.pow_succ]

private theorem nsmul_cancel {M : Type} [AddCommGroup M] [Module.Free ℤ M] {k : ℕ} (hk : 0 < k) {x y : M}
    (h : k • x = k • y) : x = y := by
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  apply smul_right_injective M hk'
  simpa only [natCast_zsmul] using h

theorem fibre_mulK : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  intro p _ D R _ b k N hk hN hkp hNp S s o K _ _ y y' hyy
  set x : Sp K ⟶ S := y ≫ o.A.hom with hx
  have hx' : y' ≫ o.A.hom = x := by
    have e := congrArg (· ≫ o.A.hom) hyy
    simp only [Category.assoc, Over.w] at e
    exact e.symm
  let T : Over S := Over.mk x
  let yt : T ⟶ o.A := Over.homMk y rfl
  let yt' : T ⟶ o.A := Over.homMk y' hx'
  have hpow : yt ^ k = yt' ^ k := by
    have e : yt ≫ (𝟙 o.A) ^ k = yt' ≫ (𝟙 o.A) ^ k := Over.OverMorphism.ext hyy
    rwa [comp_pow, comp_pow, Category.comp_id, Category.comp_id] at e
  set d : T ⟶ o.A := yt⁻¹ * yt' with hd
  have hdk : d ^ k = 1 := by rw [hd, mul_pow, inv_pow, hpow, inv_mul_cancel]
  have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
  obtain ⟨I, hI⟩ := o.geom K x _ hβ
  have hcop : (N * k * k).Coprime p := Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hkp) hkp
  have hpos : 0 < N * k * k := Nat.mul_pos (Nat.mul_pos hN hk) hk
  obtain ⟨z, hz⟩ := (I.onto (N * k * k) hpos hcop d).1 (by
    rw [pow_mul, pow_right_comm, hdk, one_pow])
  have hkz : I.ev (N * k * k) (k • z) = 1 := by rw [ev_nsmul', hz, hdk]
  obtain ⟨w, hw⟩ := (I.ker (N * k * k) hpos hcop _).1 hkz
  haveI := D.freeLa
  have hzw : z = (N * k) • w := by
    apply nsmul_cancel hk
    rw [hw, smul_smul, show k * (N * k) = N * k * k by ring]
  have key : ∀ a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y' ↔ toUnit T ≫ a.1 = d := by
    intro a
    have e1 : yt ≫ transl a.1 = yt * (toUnit T ≫ a.1) := by
      rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (yt ≫ toUnit o.A) (toUnit T)]
    constructor
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := Over.OverMorphism.ext h
      rw [e1] at e2
      rw [hd, ← e2, inv_mul_cancel_left]
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := by rw [e1, h, hd, mul_inv_cancel_left]
      exact congrArg CommaMorphism.left e2
  have hmem : o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) ∈ heckeSub o LinearMap.id (N * k) :=
    mem_heckeSub o _ _ w
  refine ⟨⟨_, hmem⟩, (key _).2 ?_, ?_⟩
  · show toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d
    rw [LinearMap.id_apply, hI, ← hzw, hz]
  · intro a ha
    have h1 : toUnit T ≫ a.1 = d := (key a).1 ha
    have h2 : toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d := by
      rw [LinearMap.id_apply, hI, ← hzw, hz]
    have hm : a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ ∈ heckeSub o LinearMap.id (N * k) :=
      Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ hmem)
    have h3 : toUnit T ≫ (a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹) = 1 := by
      have hi : toUnit T ≫ (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ = d⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← h2, ← comp_mul, inv_mul_cancel, comp_one]
      rw [comp_mul, h1, hi, mul_inv_cancel]
    have h4 := (heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul_left hNp hkp) S s o).2 K x _ hm h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)

end GlobalTheory.UPel.HT.Hecke.FibreMulK
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.baseChangeTensorSectionsHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  first | exact @GlobalTheory.Obs.BC.tensHom_bijective | exact GlobalTheory.Obs.BC.tensHom_bijective | (intros; apply GlobalTheory.Obs.BC.tensHom_bijective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affineOpensPreimage_baseChange_isBasis : ∀ (X₀ X₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) [IsAffineHom pr], (∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U) → (∀ (x : X₁) (U : X₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : X₁) (U : X₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.preAff pr).obj t₃).unop.1 ≤ U) := by
  first | exact @GlobalTheory.Obs.BC.preAff_basis | exact GlobalTheory.Obs.BC.preAff_basis | (intros; apply GlobalTheory.Obs.BC.preAff_basis <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affinePairPreimage_baseChange_fst_isBasis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  first | exact @GlobalTheory.Obs.BC.pairBC_fst_basis | exact GlobalTheory.Obs.BC.pairBC_fst_basis | (intros; apply GlobalTheory.Obs.BC.pairBC_fst_basis <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  first | exact @GlobalTheory.Obs.BC.tensPair_extMap_pairPull | exact GlobalTheory.Obs.BC.tensPair_extMap_pairPull | (intros; apply GlobalTheory.Obs.BC.tensPair_extMap_pairPull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.natural_bijective_coefficients_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R) (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b)) (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b), (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  first | exact @GlobalTheory.Obs.BC.natCoef_pull1_bijective | exact GlobalTheory.Obs.BC.natCoef_pull1_bijective | (intros; apply GlobalTheory.Obs.BC.natCoef_pull1_bijective <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DerivAtOrigin

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := by
  intro i; simp

theorem count_cons_eq {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [List.count_cons]
  · simp [List.count_cons, Pi.single_apply, h, Ne.symm h]

theorem risingFactor_ne_zero {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by
  unfold risingFactor
  rw [Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have : ((k : ℂ) + j) = ((k + j : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by omega : k + j ≠ 0)

theorem term_origin {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by
  unfold term
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem derivFormula_of_series : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (L : Set E), 4 ≤ k → (∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits L => dTerm φ k m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) (∑' q : modUnits L, dTerm φ k (m + Pi.single i 1) z q.1.out) z (Pi.single i 1)) → DerivFormula φ k L := by
  intro E _ _ I _ _ φ k L hk H
  set T : (I → ℕ) → (I → ℂ) → ℂ := fun m w => ∑' q : modUnits L, dTerm φ k m w q.1.out with hT
  have hT0 : ∀ z ∈ polydisc I, HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) (T 0 z) := by
    intro z hz
    have e : (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) = fun q : modUnits L => dTerm φ k 0 z q.1.out :=
      funext fun q => (dTerm_zero φ k z q.1.out).symm
    rw [e]
    exact (H 0 z hz).1.hasSum

  have hagree : ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, g z = (cWt E k : ℂ) * T 0 z := by
    intro g hg z hz
    obtain ⟨G, hG, hgz⟩ := hg z hz
    rw [hgz, (hG.1 (by omega)).unique (hT0 z hz)]

  have hiter : ∀ g, IsDefSum φ k L g → ∀ l : List I, ∀ z ∈ polydisc I,
      iterD l g z = (cWt E k : ℂ) * T (fun j => l.count j) z := by
    intro g hg l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      exact hagree g hg z hz
    | cons i l ih =>
      intro z hz
      have hev : iterD l g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T (fun j => l.count j) w := by
        filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using ih w hw
      have hd : HasLineDerivAt ℂ (fun w => (cWt E k : ℂ) * T (fun j => l.count j) w)
          ((cWt E k : ℂ) * T ((fun j => l.count j) + Pi.single i 1) z) z (Pi.single i 1) := by
        have h1 := (H (fun j => l.count j) z hz).2.2 i
        unfold HasLineDerivAt at h1 ⊢
        exact h1.const_mul _
      have h2 : iterD (i :: l) g z = lineDeriv ℂ (iterD l g) z (Pi.single i 1) := rfl
      rw [h2, hev.lineDeriv_eq, hd.lineDeriv, count_cons_eq]
  refine ⟨⟨fun z => (cWt E k : ℂ) * T 0 z, fun z hz => ⟨T 0 z, ⟨fun _ => hT0 z hz, fun h => by omega⟩, rfl⟩⟩, ?_⟩
  intro g hg
  refine ⟨?_, ?_⟩
  · intro z hz
    have hev : g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T 0 w := by
      filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using hagree g hg w hw
    have hda : DifferentiableAt ℂ (fun w => (cWt E k : ℂ) * T 0 w) z :=
      ((H 0 z hz).2.1).const_mul _
    exact (hda.congr_of_eventuallyEq hev).differentiableWithinAt
  · intro κ l hl
    have hκ : (fun j => l.count j) = κ := funext hl
    have h0 : iterD l g 0 = (cWt E k : ℂ) * T κ 0 := by
      rw [hiter g hg l 0 (zero_mem_polydisc I), hκ]
    have hTκ : T κ 0 = risingFactor k κ *
        ∑' q : modUnits L, ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i) := by
      simp only [hT, dTerm_origin]
      exact tsum_mul_left
    refine ⟨?_, ?_⟩
    · intro S hS
      have hS0 := hS.2 0 (by
        have : (4 : ℝ) ≤ k := by exact_mod_cast hk
        simp; linarith)
      simp only [term_origin] at hS0
      rw [h0, hTκ, hS0.tsum_eq]; ring
    · intro _
      have hsum : Summable (fun q : modUnits L =>
          ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) := by
        have h := (H κ 0 (zero_mem_polydisc I)).1
        simp only [dTerm_origin] at h
        exact (summable_mul_left_iff (risingFactor_ne_zero k (by omega) κ)).1 h
      refine ⟨_, hsum.hasSum, ?_⟩
      rw [h0, hTκ]; ring

end GlobalTheory.DerivAtOrigin
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum

theorem hasDerivAt_inv_pow_affine (c a b : ℂ) (n : ℕ) (u : ℂ) (hu : a + u * b ≠ 0) :
    HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (-(n : ℂ) * b * (a + u * b)⁻¹ ^ (n + 1))) u := by
  have h1 : HasDerivAt (fun t : ℂ => a + t * b) b u := by
    simpa using ((hasDerivAt_id u).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u :=
    ((h1.inv hu).pow n).const_mul c
  refine h2.congr_deriv ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring

theorem defCoord_ne_zero {E : Type} [Field E] [NumberField E] {I : Type} (φ : I → E →+* ℂ) (z : I → ℂ)
    (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have hφ : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx
  have hpos : 0 < ‖φ i x‖ := norm_pos_iff.mpr hφ
  have hz1 : ‖z i‖ < 1 := hz i
  unfold defCoord at h
  have heq : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [heq]
    rw [norm_neg, norm_mul, Complex.norm_conj]
  have hlt := mul_lt_of_lt_one_left hpos hz1
  linarith

theorem hasFDerivAt_dTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ)
    (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x)
      (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  intro E _ _ I _ _ φ k m x hx z hz
  set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) *
    (starRingEnd ℂ (φ i x)) ^ m i with hC
  have hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i))
      ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) z := by
    intro i
    have h1 := hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i)
      (defCoord_ne_zero φ z hz x hx i)
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)
    exact h2
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hfun : (fun w : I → ℂ => dTerm φ k m w x) =
      (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  symm
  unfold dTerm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hC, hij]
  · simp only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]
    push_cast
    ring

end GlobalTheory.DeformedSum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Z : Scheme.{0}} {k : ℕ}

def GermRatioAgree {L : LB X} (v v' : Z ⟶ X) (s₀ : H0 L k) (i i'' : Fin 1 → L.ι) (z : Z) : Prop :=
  v z ∈ secChart L i ∧ v' z ∈ secChart L i'' ∧
    IsUnit (secGerm v z s₀ i) ∧ IsUnit (secGerm v' z s₀ i'') ∧
    ∀ s₁ : H0 L k, secGerm v z s₁ i * secGerm v' z s₀ i'' = secGerm v z s₀ i * secGerm v' z s₁ i''

end GlobalTheory.Mum
end
end
