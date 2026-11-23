module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle059
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CubicUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def ev {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : Γ(Z.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom.toMonoidHom u

theorem ev_val {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : (ev x u).val = x.left.appTop.hom u.val := rfl

theorem ev_comp {W Z Y : Over S} (p : W ⟶ Z) (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev p (ev x u) = ev (p ≫ x) u := by
  ext
  rw [ev_val, ev_val, ev_val, Over.comp_left, GlobalTheory.FunDescent.comp_appTop_apply]

theorem ev_mul {Z Y : Over S} (x : Z ⟶ Y) (u v : Γ(Y.left, ⊤)ˣ) : ev x (u * v) = ev x u * ev x v := by
  simp only [ev, map_mul]

theorem ev_inv {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev x u⁻¹ = (ev x u)⁻¹ := by
  simp only [ev, map_inv]

theorem exists_char (Y : Over S) [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), ev (lift t y) ρ = chV t χ := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val := by
    intro Z t t' y
    have := congrArg Units.val (hρ Z t t' y)
    simpa [ev_val] using this
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y => ?_⟩
  ext
  rw [ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]

theorem eq_zero_of_chV (Y : Over S) [ConnectedSpace Y.left] (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t χ = 1) : χ = 0 := by
  have key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) →
      ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val := by
    intro ψ hψ
    have := congrArg Units.val (hψ _ (fst (splitTorus S X) Y))
    rw [chV_val] at this
    rw [this, Units.val_one]
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val *
          (lift t' y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val := by
    intro Z t t' y
    simp
  obtain ⟨ψ, -, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y 1 hm
  rw [huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]

private lemma mul_inv_inv_eq_of_mul_mul_mul_eq {M : Type*} [CommGroup M] (A AB a b y AY BY : M)
    (c : A * a * b * y = AB * AY * BY) :
    A * AB⁻¹ * y⁻¹ = AY * a⁻¹ * y⁻¹ * (BY * b⁻¹ * y⁻¹) := by
  apply Additive.ofMul.injective
  have c2 := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at c2 ⊢
  have hA : Additive.ofMul A = Additive.ofMul AB + Additive.ofMul AY + Additive.ofMul BY -
      (Additive.ofMul a + Additive.ofMul b + Additive.ofMul y) := by
    rw [← c2]
    abel
  rw [hA]
  abel

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {M : Type*} [CommGroup M] {p a b : M} (h : p * a⁻¹ * b⁻¹ = 1) : p = a * b := by
  rw [_root_.mul_assoc, ← _root_.mul_inv_rev, _root_.mul_inv_eq_one] at h
  rw [h, _root_.mul_comm]

end GlobalTheory.CubicUnit

namespace GlobalTheory
open CubicUnit

theorem even_cubic_unit_eq_one :
    (GlobalFnsSt → ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ), (∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) → U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) → u = 1) := by
  intro hG S _ X _ _ G _ _ _ Q u hU
  haveI := Q.i_hom
  haveI := Q.q_hom
  haveI := Q.q_flat
  haveI := Q.q_surj
  haveI := Q.q_affine

  have hval : ∀ T : Over S, ∀ x : T ⟶ G, (fun x : T ⟶ G => (ev x u).val) x = x.left.appTop.hom u.val :=
    fun T x => ev_val x u
  have h1 : ∀ T : Over S, ev (1 : T ⟶ G) u = 1 := fun T =>
    Units.ext (by simpa using (hU T _ (hval T)).1)
  have hinv : ∀ (T : Over S) (x : T ⟶ G), ev x⁻¹ u = ev x u := fun T x =>
    Units.ext ((hU T _ (hval T)).2.1 x)
  have hcub : ∀ (T : Over S) (x y v : T ⟶ G),
      ev (x * y * v) u * ev x u * ev y u * ev v u = ev (x * y) u * ev (x * v) u * ev (y * v) u :=
    fun T x y v => Units.ext (by simpa only [Units.val_mul] using (hU T _ (hval T)).2.2 x y v)

  let ρ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ :=
    ev ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G) u *
      (ev (fst (splitTorus S X) G ≫ Q.i) u)⁻¹ * (ev (snd (splitTorus S X) G) u)⁻¹
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift t y) ρ = ev ((t ≫ Q.i) * y) u * (ev (t ≫ Q.i) u)⁻¹ * (ev y u)⁻¹ := by
    intro Z t y
    simp only [ρ, ev_mul, ev_inv, ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hmul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ := by
    intro Z t t' y
    rw [hρ, hρ, hρ, MonObj.mul_comp]
    exact mul_inv_inv_eq_of_mul_mul_mul_eq _ _ _ _ _ _ _ (hcub Z (t ≫ Q.i) (t' ≫ Q.i) y)
  obtain ⟨χ, hχ⟩ := exists_char G ρ hmul

  have hsplit : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev ((t ≫ Q.i) * y) u = ev (t ≫ Q.i) u * ev y u := by
    intro Z t y
    have e1 := hχ Z t y
    have e0 := hχ Z t 1
    rw [hρ] at e1 e0
    simp only [_root_.mul_one, h1, _root_.inv_one, _root_.mul_inv_cancel] at e0
    rw [← e0] at e1
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one e1

  let ρ₂ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ := ev (fst (splitTorus S X) G ≫ Q.i) u
  have hρ₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ₂ = ev (t ≫ Q.i) u := by
    intro Z t y
    simp only [ρ₂, ev_comp, lift_fst_assoc]
  have hmul₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ₂ = ev (lift t y) ρ₂ * ev (lift t' y) ρ₂ := by
    intro Z t t' y
    rw [hρ₂, hρ₂, hρ₂, MonObj.mul_comp, hsplit]
  obtain ⟨ψ, hψ⟩ := exists_char G ρ₂ hmul₂
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = chV t ψ := fun Z t => by
    rw [← hρ₂ Z t 1, hψ]
  have h2ψ : ψ + ψ = 0 := by
    refine eq_zero_of_chV G (ψ + ψ) fun Z t => ?_
    have e := hinv Z (t ≫ Q.i)
    rw [← GrpObj.inv_comp, hψ', hψ', chV_inv] at e
    rw [chV_add]
    calc chV t ψ * chV t ψ = (chV t ψ)⁻¹ * chV t ψ := by rw [e]
      _ = 1 := _root_.inv_mul_cancel _
  have hψ0 : ψ = 0 := by
    rw [← two_zsmul] at h2ψ
    exact (smul_eq_zero.mp h2ψ).resolve_left (by norm_num)
  have htor : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = 1 := fun Z t => by
    rw [hψ', hψ0, chV_zero]
  have hsec : (1 : 𝟙_ (Over S) ⟶ G).left.appTop.hom u.val = 1 := by
    rw [← ev_val, h1, Units.val_one]

  have L : ∀ {Z : Scheme.{0}} (k : Z ⟶ G.left) (h : ⊤ ≤ k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤))
      (f : Γ(G.left, Q.q.left ⁻¹ᵁ ⊤)), (k.appLE (Q.q.left ⁻¹ᵁ ⊤) ⊤ h).hom f = k.appTop.hom f := by
    intro Z k h f
    show (k.appLE _ (k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) le_rfl).hom f = _
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.invariant_functions_descend S G Q.B (splitTorus S X) Q.q Q.i Q.q_hom Q.i_hom
    Q.q_flat Q.q_surj inferInstance Q.isKernel ⊤).2.2 u.val (fun Z t g h₁ h₂ => by
      have e := congrArg Units.val
        (show ev ((t ≫ Q.i) * g) u = ev g u by rw [hsplit, htor, _root_.one_mul])
      rw [ev_val, ev_val] at e
      exact (L _ _ _).trans (e.trans (L _ _ _).symm))
  have hq : Q.q.left.appTop.hom a = u.val := ha
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilCube.surj_fst hG Q.isAb (𝟙_ (Over S))
    ((snd (𝟙_ (Over S)) Q.B).left.appTop.hom a)
  have hB : a = (toUnit Q.B).left.appTop.hom c₀ := by
    have e := congrArg (lift (toUnit Q.B) (𝟙 Q.B)).left.appTop.hom hc₀
    rw [← GlobalTheory.FunDescent.comp_appTop_apply, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_snd, Over.id_left] at e
    simpa using e.symm
  have hG0 : u.val = (toUnit G).left.appTop.hom c₀ := by
    rw [← hq, hB, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique (Q.q ≫ toUnit Q.B) (toUnit G)]
  have hc : c₀ = 1 := by
    have e := hsec
    rw [hG0, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G) ≫ toUnit G) (𝟙 _), Over.id_left] at e
    simpa using e
  exact Units.ext (by rw [hG0, hc, map_one, Units.val_one])

end GlobalTheory
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem TQ.exists_affine_weight_units [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ V : Q.B.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ : X, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Module.Free.chooseBasis ℤ X
  choose W hW v hv using fun k => Q.loc b (e k)
  have ho : IsOpen (⋂ k, (W k : Set Q.B.left)) := isOpen_iInter_of_finite fun k => (W k).isOpen
  obtain ⟨V, hV, hbV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Q.B.left.isBasis_affineOpens
    (show b ∈ (⟨_, ho⟩ : Q.B.left.Opens) from Set.mem_iInter.2 hW)
  have hk : ∀ k, Q.q.left ⁻¹ᵁ V ≤ Q.q.left ⁻¹ᵁ W k := fun k =>
    Q.q.left.preimage_mono fun x hx => Set.mem_iInter.1 (hle hx) k
  let w : _ → Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := fun k =>
    Units.map (G.left.presheaf.map (homOfLE (hk k)).op).hom.toMonoidHom (v k)
  let l : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt Q.i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show IsWt Q.i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact isWt_one
      add_mem' := fun {a c} ha hc => by
        show IsWt Q.i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show IsWt Q.i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact IsWt.inv ha }
  have hH : Submodule.span ℤ (Set.range e) ≤ H.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show IsWt Q.i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis]
    exact (hv k).res (hk k)
  refine ⟨V, hV, hbV, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  exact hH (e.mem_span χ)

theorem TQ.exists_local_section [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ (V : Q.B.left.Opens) (hV : IsAffineOpen V), b ∈ V ∧
      ∃ s : Spec Γ(Q.B.left, V) ⟶ G.left, s ≫ Q.q.left = hV.fromSpec := by
  obtain ⟨V, hV, hb, u, hu⟩ := Q.exists_affine_weight_units b
  have := Q.q_affine
  obtain ⟨hU, hbij⟩ := isAffineOpen_and_bijective_of_weight_units S X G Q.B Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V hV u hu
  let φ := RingEquiv.ofBijective _ hbij
  let ε : AddMonoidAlgebra Γ(Q.B.left, V) X →+* Γ(Q.B.left, V) :=
    (AddMonoidAlgebra.lift Γ(Q.B.left, V) Γ(Q.B.left, V) X 1).toRingHom
  let r : Γ(G.left, Q.q.left ⁻¹ᵁ V) ⟶ Γ(Q.B.left, V) := CommRingCat.ofHom (ε.comp φ.symm.toRingHom)
  have hr : Q.q.left.appLE V _ le_rfl ≫ r = 𝟙 _ := by
    rw [← Scheme.Hom.app_eq_appLE]
    ext a
    have h : φ (AddMonoidAlgebra.single 0 a) = (Q.q.left.app V).hom a :=
      (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans
        ((congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    change ε (φ.symm ((Q.q.left.app V).hom a)) = a
    rw [← h, RingEquiv.symm_apply_apply]
    simp [ε]
  refine ⟨V, hV, hb, Spec.map r ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Q.q.left hV hU le_rfl, ← Category.assoc,
    ← Spec.map_comp, hr, Spec.map_id, Category.id_comp]

theorem TQ.exists_lift [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A : Type} [CommRing A] [IsLocalRing A] {p : Spec (CommRingCat.of A) ⟶ S} (b : Over.mk p ⟶ Q.B) :
    ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b := by
  let b' : Spec (CommRingCat.of A) ⟶ Q.B.left := b.left
  obtain ⟨V, hV, hb, s, hs⟩ := Q.exists_local_section (b' (IsLocalRing.closedPoint A))
  have hr : Set.range b' ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) b' hb).ge (Set.mem_univ y)
  have h : (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ≫ Q.q.left = b' := by
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
  refine ⟨Over.homMk (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w Q.q, ← Category.assoc]
  exact (congrArg (· ≫ Q.B.hom) h).trans (Over.w b)

theorem exists_pow_eq_splitTorus [Module.Free ℤ X] {Z : Over S} {N : ℕ}
    (h : ∀ a : Γ(Z.left, ⊤)ˣ, ∃ r, r ^ N = a) (t : Z ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, t' ^ N = t := by
  let e := Module.Free.chooseBasis ℤ X
  let E := splitTorusPointsEquiv S X Z
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := (MonoidHom.toAdditiveRight (E t)).toIntLinearMap
  have hl : N • l = m := e.ext fun k => by
    rw [LinearMap.smul_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨E.symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom), E.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem torusQuotient_points_lift :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (A : Type) [CommRing A] [IsLocalRing A] (p : Spec (CommRingCat.of A) ⟶ S),
      (∀ b : Over.mk p ⟶ Q.B, ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b) ∧
      ∀ N : ℕ, (∀ a : Aˣ, ∃ r : Aˣ, r ^ N = a) → ∀ b : Over.mk p ⟶ Q.B, b ^ N = 1 →
        ∃ g : Over.mk p ⟶ G, g ^ N = 1 ∧ g ≫ Q.q = b := by
  intro S X _ _ _ G _ _ Q A _ _ p
  refine ⟨Q.exists_lift, fun N hN b hb => ?_⟩
  have := Q.q_hom
  have := Q.i_hom
  obtain ⟨g, rfl⟩ := Q.exists_lift b
  have h₁ : (g ^ N) ≫ Q.q = toUnit _ ≫ η[Q.B] := by rw [MonObj.pow_comp, hb, Hom.one_def]
  let e : Aˣ ≃* Γ(Spec (CommRingCat.of A), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨t, ht⟩ := exists_pow_eq_splitTorus (Z := Over.mk p) (N := N) (fun a => by
    obtain ⟨r, hr⟩ := hN (e.symm a)
    exact ⟨e r, (map_pow e r N).symm.trans ((congrArg e hr).trans (e.apply_symm_apply a))⟩)
    (Q.isKernel.lift _ _ h₁)
  have h₂ : (t ≫ Q.i) ^ N = g ^ N := by rw [← MonObj.pow_comp, ht, IsPullback.lift_fst]
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  refine ⟨(t ≫ Q.i)⁻¹ * g, ?_, ?_⟩
  · rw [mul_pow, inv_pow, h₂, inv_mul_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, h₃, inv_one, _root_.one_mul]

end GlobalTheory.UU
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericPol

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_lift {K : Type} [Field K] {X Z : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) (j : Z ⟶ X)
    (h : Set.range x ⊆ Set.range j) :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (z : Spec (CommRingCat.of K') ⟶ Z), specOf i ≫ x = z ≫ j := by
  obtain ⟨z, hz⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := j) _ z hz.symm
  let u := (pullback x j).fromSpecResidueField p
  refine ⟨(pullback x j).residueField p, inferInstance, (Spec.preimage (u ≫ pullback.fst x j)).hom,
    u ≫ pullback.snd x j, ?_⟩
  have e : specOf (Spec.preimage (u ≫ pullback.fst x j)).hom = u ≫ pullback.fst x j :=
    Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E}

theorem proper_ample_kTriv {X Z : Scheme.{0}} {T : SAB H X} {T' : SAB H Z} {j : Z ⟶ X} (mj : SABMap T' T j)
    (hp : IsProper T'.G.hom) (hA : RelAmple T'.G T'.PP.L) (hK : KTriv T'.G T'.PP.L) {K : Type} [Field K]
    {x : Spec (CommRingCat.of K) ⟶ X} {t : SAB H (Spec (CommRingCat.of K))} (m : SABMap t T x)
    (h : Set.range x ⊆ Set.range j) : IsProper t.G.hom ∧ RelAmple t.G t.PP.L ∧ KTriv t.G t.PP.L := by
  obtain ⟨K', _, i, z, e⟩ := exists_lift x j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull CubePf.cubePull (specOf i) t
  generalize (⟨(Over.pullback (specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ T T' t' j z mj (e ▸ n)
  obtain ⟨w, g, -⟩ := m'.lin
  obtain ⟨w₁, g₁, -⟩ := m₁.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K')) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension K K' i t.G t'.G m₁.φ m₁.cart t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ⟨w₁, g₁⟩
    (MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hp)
    (relAmple_pull m'.cart.1 T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA)
    (kTriv_pull m'.cart T'.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK)

def toPolAV {S : Scheme.{0}} (t : SAB H S) (g : ℕ) (hg : SmoothOfRelativeDimension g t.G.hom) (hp : IsProper t.G.hom)
    (hA : RelAmple t.G t.PP.L) (hK : KTriv t.G t.PP.L) : PolAV S where
  A := t.G
  isAb := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := hA
  ktriv := hK

theorem rosatiAdj {S : Scheme.{0}} (t : SAB H S) (a : NumberField.RingOfIntegers E) :
    RosatiAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) := by
  obtain ⟨u, hu⟩ := GlobalTheory.NormRos.exists_gen_rosati t.PP.isLB _ _ (t.adj a)
  exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ u _, DVR.pullGen_isGen _ _ _ _ hu _⟩

end GlobalTheory.GenericPol


open GlobalTheory.GenericPol ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem GlobalTheory.exists_polAV_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (χ : Geo.Tor.Sp R ⟶ Y.X) (t : Geo.Tor.SAB H (Geo.Tor.Sp R)) (_ : Geo.Tor.SABMap t Y.t χ), Set.range (jK R ≫ χ) ⊆ Set.range Y.j → ∀ g : ℕ, SmoothOfRelativeDimension g t.G.hom → ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj t.G ≅ A.A) (oA : letI := H.starRing; A.OAct (NumberField.RingOfIntegers E)), A.g = g ∧ IsMonHom eA.hom ∧ Geo.Tor.LBIso (A.L.pull eA.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ (letI := H.starRing; ∀ a, (Over.pullback (jK R)).map (t.act.act a) ≫ eA.hom = eA.hom ≫ oA.act a) := by
  intro E _ _ _ H Dm l Xo c O _ β Y R _ _ χ t m h g hg
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₀
  obtain ⟨hp, hA, hK⟩ := proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv n h
  have hg' : SmoothOfRelativeDimension g t'.G.hom := by
    show SmoothOfRelativeDimension g (pullback.snd t.G.hom (jK R))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  refine ⟨toPolAV t' g hg' hp hA hK, Iso.refl _, ⟨t'.act.toRingAct, rosatiAdj t'⟩, rfl, ?_, ?_, fun a => ?_⟩
  · exact inferInstanceAs (IsMonHom (𝟙 t'.G))
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end
end
