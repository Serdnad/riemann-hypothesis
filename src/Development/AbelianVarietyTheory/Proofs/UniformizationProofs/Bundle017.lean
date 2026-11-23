module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtTorsionPoints

section Values

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_pull (hL : L.IsLB) (ρ : Z ⟶ Y) (hinj : ∀ U, Function.Injective (ρ.app U).hom)
    (hρ : ∀ a b : Y ⟶ X, ρ ≫ a = ρ ≫ b → a = b)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (hinj _ (fn_ext fun z hz => ?_))
  have hz' : ρ z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => ρ ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e <;> replace e := hρ _ _ e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz'.1 a, Set.mem_iInter.1 hz'.2 a])
  have := h z J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  rw [gs_pull (𝟙 Z) ρ z _ hz', gs_pull (𝟙 Z) ρ z _ hz', Category.id_comp, gs_unit ρ z _ hz', gs_unit ρ z _ hz']
  exact congrArg Units.val ((gm_res ρ z _ hz' _).trans (this.trans (gm_res ρ z _ hz' _).symm))

end Values

section Valuation

variable {S F : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Algebra S F] [IsFractionRing S F]

end Valuation

section Main

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T)

variable {z : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}

end Main

end GlobalTheory.GtTorsionPoints
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankBundle

variable {X : Scheme.{0}}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) : gs (𝟙 X) x U 1 = 1 := by
  rw [gs_eq (𝟙 X) x U h, map_one, map_one]

theorem mem_basicOpen_iff (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)) :
    x ∈ X.basicOpen a ↔ IsUnit (gs (𝟙 X) x U a) := by
  rw [gs_eq (𝟙 X) x U h]
  exact X.mem_basicOpen a x h

theorem sec_compat {N : LB X} (s : LB.Sec N) (x : X) {k k' : N.ι} (hk : x ∈ N.U k) (hk' : x ∈ N.U k') :
    gs (𝟙 X) x (N.U k) (s.f k) = (gm (𝟙 X) x (N.U k ⊓ N.U k') (N.g k k')).val * gs (𝟙 X) x (N.U k') (s.f k') := by
  have hm : x ∈ N.U k ⊓ N.U k' := ⟨hk, hk'⟩
  exact (gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans
    ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))

theorem exists_ratio {U : X.Opens} (a b : Γ(X, U)) : ∃ r : Γ(X, X.basicOpen b), ∀ x ∈ X.basicOpen b,
    gs (𝟙 X) x (X.basicOpen b) r * gs (𝟙 X) x U b = gs (𝟙 X) x U a := by
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩
  rw [← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a,
    ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_rank_one_bundle : ∀ (X : Scheme.{0}) (N : LB X) (n m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → ∃ (H' : LB X) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB ∧ (⨆ i, nonzeroLocus (s' i) = ⊤) ∧ ∀ (x : X) (c : H'.ι), x ∈ H'.U c → ∃ j, ∀ k, x ∈ N.U k → ∃ v : (X.presheaf.stalk x)ˣ, ∀ i, gs (𝟙 X) x (N.U k) ((w i j).f k) = v.val * gs (𝟙 X) x (H'.U c) ((s' i).f c) := by
  intro X N n m w hN hcov hr
  choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) =>
    exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)
  let U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens := fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)
  have hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2 := fun c x hx => X.basicOpen_le _ hx
  have hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2)) := fun c x hx =>
    (mem_basicOpen_iff x _ (hle c x hx) _).1 hx
  have one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1 := fun c x hx =>
    (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)
  have key : ∀ l c c' x, x ∈ U c → x ∈ U c' →
      gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c') := by
    intro l c c' x hx hx'
    have e₁ := hS l c x hx
    have e₂ := hS c'.1 c x hx
    have e₃ := hS l c' x hx'
    have e₄ := congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)
    rw [gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx),
      sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'),
      sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')] at e₄
    apply (((hu c x hx).mul (hu c' x hx')).mul
      (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel
    rw [← e₁, ← e₂, ← e₃] at e₄
    exact Eq.trans (by ring) (e₄.trans (by ring))
  have hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c)) := fun c c' =>
    IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by
      rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2,
        one c x hx.1, gs_one x _ hx])
  have gv : ∀ c c' x, x ∈ U c ⊓ U c' →
      (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c) := fun c c' x hx =>
    (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)
  have ex : ∀ x : X, ∃ c, x ∈ U c := fun x => by
    have hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j) := by rw [hcov]; trivial
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨k, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨(i, j, k), hx⟩
  let H : LB X := ⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩
  let s : Fin (n + 1) → LB.Sec H := fun l => ⟨S l, fun c c' => fn_ext fun x hx =>
    (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩
  refine ⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩
  · exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)
  · rw [gm_res (𝟙 X) x _ hx, map_one, Units.val_one]
    exact (gv c c x ⟨hx, hx⟩).trans (one c x hx)
  · rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]
    exact (congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans
      ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)
  · refine top_unique fun x _ => ?_
    obtain ⟨c, hc⟩ := ex x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩
    exact (mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)
  · intro x c hc
    refine ⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩
    rw [sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]
    exact congrArg _ (_root_.mul_comm _ _)

end GlobalTheory.RankBundle
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusCube

open Rosenlicht SplitTorusPoints Geo.Tor

theorem toHom_comp_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z W : Over S} (ρ : W ⟶ Z)
    (t : Z ⟶ splitTorus S X) (a : Multiplicative X) :
    (toHom (ρ ≫ t) a).val = ρ.left.appTop.hom (toHom t a).val := by
  change (coord (ρ ≫ t)).hom _ = _
  rw [coord_comp]; rfl

theorem toHom_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} :
    toHom (1 : Z ⟶ splitTorus S X) = 1 :=
  map_one (splitTorusPointsEquiv S X Z)

theorem exists_form (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of k), ⊤)) (a b d : X), IsUnit c ∧
      ∀ (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X),
        (lift x (lift y u)).left.appTop.hom w = Z.hom.appTop.hom c *
          ((toHom x (Multiplicative.ofAdd a)).val * (toHom y (Multiplicative.ofAdd b)).val *
            (toHom u (Multiplicative.ofAdd d)).val) := by
  let Y := splitTorus (Spec (.of k)) (X × X × X)
  have hp : ∀ j : X →+ X × X × X, ∃ p : Y ⟶ splitTorus (Spec (.of k)) X,
      ∀ (Z : Over (Spec (.of k))) (ρ : Z ⟶ Y) (a : X),
        toHom (ρ ≫ p) (Multiplicative.ofAdd a) = toHom ρ (Multiplicative.ofAdd (j a)) := by
    intro j
    obtain ⟨p, hp⟩ := (toHom_bijective (Z := Y) (X := X)).2
      ((toHom (𝟙 Y)).comp (AddMonoidHom.toMultiplicative j))
    refine ⟨p, fun Z ρ a => Units.ext ?_⟩
    rw [toHom_comp_val, hp]
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  obtain ⟨p₀, h₀⟩ := hp (AddMonoidHom.inl _ _)
  obtain ⟨p₁, h₁⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  obtain ⟨p₂, h₂⟩ := hp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _))
  obtain ⟨c, ⟨a, b, d⟩, hc, e⟩ := torus_units k (X × X × X)
    (hw.map (lift p₀ (lift p₁ p₂)).left.appTop.hom)
  refine ⟨c, a, b, d, hc, fun Z x y u => ?_⟩
  obtain ⟨ρ, hρ⟩ := (toHom_bijective (Z := Z) (X := X × X × X)).2
    ((toHom x).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)) *
      (toHom y).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _))) *
      (toHom u).comp (AddMonoidHom.toMultiplicative
        ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  have r₀ : ρ ≫ p₀ = x := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₀ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₁ : ρ ≫ p₁ = y := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₁ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have r₂ : ρ ≫ p₂ = u := toHom_bijective.1 (MonoidHom.ext fun a => by
    refine (h₂ Z ρ a.toAdd).trans ?_
    rw [hρ]; simp)
  have hl : lift x (lift y u) = ρ ≫ lift p₀ (lift p₁ p₂) := by
    rw [comp_lift, comp_lift, r₀, r₁, r₂]
  have hχ : ρ.left.appTop.hom (chi (X × X × X) (a, b, d)) =
      (toHom ρ (Multiplicative.ofAdd (a, b, d))).val := by
    conv_rhs => rw [← Category.comp_id ρ, toHom_comp_val]
    rfl
  rw [hl, ← over_appTop_comp, e, map_mul, hχ, hρ, ← appTop_comp_apply, Over.w]
  simp

theorem unit_eq_one (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w)
    (h₀ : (lift (𝟙 _) (lift 1 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₁ : (lift 1 (lift (𝟙 _) 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₂ : (lift 1 (lift 1 (𝟙 _)) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X) :
    (lift x (lift y u)).left.appTop.hom w = 1 := by
  obtain ⟨c, a, b, d, hc, H⟩ := exists_form k X w hw
  rw [H] at h₀ h₁ h₂
  simp only [toHom_one, MonoidHom.one_apply, Units.val_one, _root_.mul_one, _root_.one_mul]
    at h₀ h₁ h₂
  have ha : a = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₀.trans (map_one _).symm)
  have hb : b = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₁.trans (map_one _).symm)
  have hd : d = 0 := torus_const_mul_chi k X (c₂ := 1) hc (h₂.trans (map_one _).symm)
  subst ha hb hd
  have hc1 : c = 1 := torus_const_injective k X (by simpa using h₀)
  rw [H, hc1]
  simp

section Val

variable {X Y : Scheme.{0}} (L : LB X)

def HasVal (form : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V)
    (f : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → L.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ (∀ (V : Type) [CommGroup V] (h : (Y ⟶ X) → V), ∏ k, h (φ k) ^ ε k = form V h) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t r z J = f Z r z J

variable {L}

theorem HasVal.mul {F F' : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f f'}
    (h : HasVal L F f) (h' : HasVal L F' f') :
    HasVal L (fun V _ k => F V k * F' V k) (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', a', b'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t',
    DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (a V k) (a' V k))
  · rw [val_mul hJ, b Z r z J hJ, b' Z r z J hJ]

theorem HasVal.inv {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) : HasVal L (fun V _ k => (F V k)⁻¹) (fun Z r z J => (f Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, a, b⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, a]
  · rw [val_inv, b Z r z J hJ]

theorem HasVal.exists_unit (hL : L.IsLB) {F : ∀ (V : Type) [CommGroup V], ((Y ⟶ X) → V) → V} {f}
    (h : HasVal L F f) (hF : ∀ (V : Type) [CommGroup V] (k : (Y ⟶ X) → V), F V k = 1) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (f Z r z J).val = gs (𝟙 Z) z ⊤ (r.appTop.hom w.val) := by
  obtain ⟨K, _, φ, ε, u, hu, a, b⟩ := h
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (a V k).trans ((hF V k).trans (Fintype.prod_empty _).symm)) u hu
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← b Z r z J hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  refine (congrArg Units.val (gm_res r z le trivial _)).symm.trans
    ((gs_unit r z ⊤ trivial _).symm.trans ?_)
  refine Eq.trans ?_ (gs_pull (𝟙 Z) r z ⊤ trivial _).symm
  rw [Category.id_comp]

end Val

end TorusCube


end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftTest

theorem stalkMap_injective_of_flat {W Z : Scheme.{0}} (f : W ⟶ Z) [Flat f] (w : W) :
    Function.Injective (f.stalkMap w).hom := by
  have h := Flat.stalkMap f w
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)) := f.toLRSHom.prop w
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.presheaf.stalk (f w)) (B := W.presheaf.stalk w)
  exact FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)

theorem gs_comp {W Z Y : Scheme.{0}} (f : W ⟶ Z) (r : Z ⟶ Y) (w : W) (U : Y.Opens) (h : r (f w) ∈ U)
    (a : Γ(Y, U)) : gs (f ≫ r) w U a = (f.stalkMap w).hom (gs r (f w) U a) := by
  rw [← gs_pull f r w U h, gs_eq f w (r ⁻¹ᵁ U) h, gs_eq r (f w) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) w h _).symm

theorem sval_eq_zero_of_flat {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (f : W ⟶ Z) [Flat f] (w : W)
    (h : ∀ J, Good L w J → sval d (f ≫ r) w J = 0) (J) (hJ : Good L (f w) J) : sval d r (f w) J = 0 := by
  choose I hI using fun χ : W ⟶ X => exists_chart hL (χ w)
  have hm : r (f w) ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have e := sec_trans d (f ≫ r) w (j := fun k => J (r ≫ φ k)) hm (Good.mem hI φ (f ≫ r))
  have e0 : gs (f ≫ r) w (LB.wchart L φ (fun k => I ((f ≫ r) ≫ φ k))) (d.f (fun k => I ((f ≫ r) ≫ φ k))) = 0 := h I hI
  rw [e0, mul_zero] at e
  exact (map_eq_zero_iff _ (stalkMap_injective_of_flat f w)).1 ((gs_comp f r w _ hm _).symm.trans e)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X L hL K _ φ ε d H Z r ⟨ρ, hρ⟩ z J hJ
  have := g.q_flat
  have := g.q_surj
  let b : Z ⟶ (thickObj R I e D.P.A).left :=
    pullback.lift (r ≫ p.left) ρ (by rw [Category.assoc, Over.w p, hρ])
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p.left := pullback.lift_fst _ _ _
  obtain ⟨w, rfl⟩ := (pullback.fst b g.q.left).surjective z
  refine sval_eq_zero_of_flat hL d r (pullback.fst b g.q.left) w (fun J' hJ' => ?_) J hJ
  refine H _ (pullback.snd b g.q.left) _ ?_ w J' hJ'
  rw [Category.assoc, ← hb, pullback.condition_assoc]
  rfl

end GlobalTheory.LiftTest
end
