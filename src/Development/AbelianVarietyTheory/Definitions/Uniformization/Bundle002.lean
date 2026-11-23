module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]

theorem TQ.comp_i_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) : (t ≫ Q.i) ≫ Q.q = 1 := by
  rw [Category.assoc, Q.isKernel.w, ← Category.assoc]
  simp only [toUnit_unique (t ≫ toUnit _) (toUnit T)]
  rfl

theorem TQ.Desc.cubV_torus {Q : TQ G X} {P : CP G} (D : Q.Desc P) {T : Over S} {z : T.left} {J}
    (hJ : Good D.M.L.L z J) (h : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S) (x : T ⟶ splitTorus S X) (y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV D.M.c (T := Over.mk (T.hom ≫ 𝟙 S)) z J
      (toBase h (x ≫ Q.i)) (toBase h y) (toBase h u)) = 1 := by
  have e : toBase h (x ≫ Q.i) = 1 := by
    ext
    have h1 := congrArg (fun f => f.left) (TQ.comp_i_q Q x)
    simp only [Over.comp_left] at h1
    rw [one_left] at h1 ⊢
    simp [toBase, h1]
  rw [e]
  exact (isCub_cubV D.M.c hJ).face _ _

private theorem comp_one_uniformization {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (x : T ⟶ T') :
    x ≫ (1 : T' ⟶ G) = 1 := by
  show x ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _)]

private theorem one_comp_of_isMonHom' {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) [IsMonHom q]
    {T : Over S} : (1 : T ⟶ G) ≫ q = 1 := by
  show (toUnit _ ≫ η) ≫ q = toUnit _ ≫ η
  rw [Category.assoc, IsMonHom.one_hom]

private theorem prod_mul_inv_four_eq_of_mul_eq {U : Type} [CommGroup U] {C w a b c d e f g : U}
    (hv : e * f * g * w = a * b * c * d * C) :
    w * a⁻¹ * (w * b⁻¹) * (w * c⁻¹) * (w * d⁻¹) = C * (w * e⁻¹) * (w * f⁻¹) * (w * g⁻¹) := by
  have hC : C = (a * b * c * d)⁻¹ * (e * f * g * w) := by rw [hv]; group
  rw [hC]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem oneGen_isGen_uniformization {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  unfold LB.Gen.IsGen
  simp [LB.oneGen]
  intro i j
  unfold LB.LinComb
  simp

private theorem mul_inv_eq_mul_mul_mul_inv {U : Type} [CommGroup U] (w m s : U) : w * m⁻¹ = s * (w * (m * s)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem eq_mul_inv_of_one_eq_mul_inv_mul {U : Type} [CommGroup U] {a b v : U} (h : 1 = a * b⁻¹ * v) : v = b * a⁻¹ := by
  calc v = (a * b⁻¹)⁻¹ * (a * b⁻¹ * v) := by group
    _ = b * a⁻¹ := by rw [← h]; group

theorem TQ.Desc.exists_even {Q : TQ G X} {P : CP G} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hi := Q.i_hom
  have hq := Q.q_hom
  have hw : PGen D.w := (isGen_iff D.w).1 D.map.gen
  have hF : FormEq (K := PEmpty) (K' := Fin 2) PEmpty.elim PEmpty.elim
      ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] ![1, -1] := by
    intro U _ h
    simp [Fin.prod_univ_two]
  obtain ⟨t, ht, htv⟩ := exists_gen D.M.L.isLB hF (LB.oneGen D.M.L.L) (oneGen_isGen_uniformization _)
  have hc : ∀ k, (![Q.i.left, (1 : splitTorus S X ⟶ G).left] : Fin 2 → _) k ≫ Q.q.left =
      𝟙 _ ≫ (![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left] : Fin 2 → _) k := by
    intro k
    fin_cases k
    · show Q.i.left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left]
      simpa using congrArg (fun f => f.left) (TQ.comp_i_q Q (𝟙 _))
    · show (1 : splitTorus S X ⟶ G).left ≫ Q.q.left = 𝟙 _ ≫ (1 : splitTorus S X ⟶ Q.B).left
      rw [Category.id_comp, ← Over.comp_left, one_comp_of_isMonHom']
  obtain ⟨a, ha, hpm⟩ := CubTransport.exists_pmaps hw D.M.L.isLB P.L.isLB (𝟙 _) hc t ht
  have key : ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J : (T.left ⟶ Q.B.left) → D.M.L.L.ι)
      (J' : (T.left ⟶ G.left) → P.L.L.ι), Good D.M.L.L z J → Good P.L.L z J' →
      val a x.left z J' = gw D.w (1 : T ⟶ G).left z (J ((1 : T ⟶ G).left ≫ Q.q.left)) (J' (1 : T ⟶ G).left) *
        (gw D.w (x ≫ Q.i).left z (J ((x ≫ Q.i).left ≫ Q.q.left)) (J' (x ≫ Q.i).left))⁻¹ := by
    intro T x z J J' hJ hJ'
    have e1 := CubTransport.val_pmaps hc hpm x.left hJ hJ'
    rw [htv _ _ _ _ hJ, val_one, Fin.prod_univ_two] at e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, ← Over.comp_left,
      comp_one_uniformization] at e1
    exact eq_mul_inv_of_one_eq_mul_inv_mul e1
  refine ⟨⟨a, ha, ?_⟩, ?_⟩
  · intro T x y u z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hv := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.2 (x ≫ Q.i) (y ≫ Q.i) (u ≫ Q.i)
    rw [TQ.Desc.cubV_torus D hJ _ x (y ≫ Q.i) (u ≫ Q.i), _root_.one_mul] at hv
    simp only [← MonObj.mul_comp] at hv
    have key' := fun v : T ⟶ splitTorus S X => key T v z J J' hJ hJ'
    simp only [key']
    exact prod_mul_inv_four_eq_of_mul_eq hv
  · intro T x z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_pt D.M.L.isLB z
    have hs := (D.map.vals T z J' J hJ' hJ (fun g => gw D.w g.left z (J (g.left ≫ Q.q.left)) (J' g.left))
      (fun _ => rfl)).2.1 (x ≫ Q.i)
    have e3 : (x ≫ Q.i).left ≫ Q.q.left = (1 : T ⟶ Q.B).left := by
      rw [← Over.comp_left, TQ.comp_i_q]
    have hsym : val D.M.sym ((x ≫ Q.i).left ≫ Q.q.left) z J = 1 := by
      rw [e3]; exact CP.val_sym_one _ hJ
    rw [hsym, _root_.one_mul, ← GrpObj.inv_comp] at hs
    rw [key T x⁻¹ z J J' hJ hJ', key T x z J J' hJ hJ', hs]
    exact mul_inv_eq_mul_mul_mul_inv _ _ _


end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.SettingConsistentExample

theorem exists_even_one {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (P : CP G)
    (i : H ⟶ G) (hi : i = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  subst hi
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ := (PEmpty.elim : PEmpty → (H.left ⟶ G.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![(1 : H ⟶ G).left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ H.left) (z : Z) (J), Good P.L.L z J → val t r z J = 1 :=
    fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨t, ht, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, MonObj.comp_one, (isCub_cubV P.c hJ).face, _root_.mul_one]
  · show val t _ z J = _ * val t _ z J
    rw [v _ _ z J hJ, v _ _ z J hJ, MonObj.comp_one, P.val_sym_one hJ, _root_.mul_one]

section Generic
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

variable (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (X : Type) [AddCommGroup X] [Subsingleton X]






omit hG' in
theorem ab_even (P : CP G) : ∃ σ : CubTriv P.c (TQ.abelian G hG X).i, σ.Even :=
  exists_even_one _ _ (Hom.one_def).symm

end Generic

section Thick
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]




end Thick

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

end GlobalTheory.UU.SettingConsistentExample
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R]

def IsCPOf (D : DegPre R) (M : CP D.P.A) : Prop :=
  M.L = ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ ∧ HEq M.c D.cub ∧ HEq M.sym D.sym

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
structure PreU (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where

  semi : IsSemiAbelian G

  gen : (Over.pullback (jK R)).obj G ≅ A.A

  gen_hom : IsMonHom gen.hom

  P : CP G

  wA : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R)))

  wA_gen : wA.IsGen

  gt : ∀ e : ℕ, GtCoord I D e G

  gt_q : ∀ e : ℕ, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left

  gt_t : ∀ (e : ℕ) (χ : D.X), LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ ((gt (e + 1)).t χ) (thickMap R I e G)) ((gt e).t χ)

  w : ∀ e : ℕ, LB.Iso (P.L.L.pull (fstG I e G).left) (D.P.L.pull (gt e).pG.left)

  w_gen : ∀ e, (w e).IsGen

  w_vals : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left)
    (JG : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good P.L.L z JG → Good D.P.L z J →
    ∀ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, W x = gw (w e) x.left z (J (x.left ≫ (gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))) →
      (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (T.hom ≫ thick R I e) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ thick R I e) z JG) ∧
      (∀ x : T ⟶ thickObj R I e G, val D.sym (x.left ≫ (gt e).pG.left) z J * W x =
        W x⁻¹ * val P.sym (x.left ≫ (fstG I e G).left) z JG) ∧
      ∀ x y u : T ⟶ thickObj R I e G,
        @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
            ((Over.map (thick R I e)).map x ≫ (gt e).pG) ((Over.map (thick R I e)).map y ≫ (gt e).pG)
            ((Over.map (thick R I e)).map u ≫ (gt e).pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map (thick R I e)).obj T) z JG
            ((Over.map (thick R I e)).map x ≫ fstG I e G) ((Over.map (thick R I e)).map y ≫ fstG I e G)
            ((Over.map (thick R I e)).map u ≫ fstG I e G))

  w_compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : D.P.L.ι) (k : P.L.L.ι),
    (gt e).pG.left (x z) ∈ D.P.L.U j → (fstG I e G).left (x z) ∈ P.L.L.U k →
    gw (w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (w e) x z j (fun _ => k)
variable {I : Ideal R} {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def famφT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (α : D.X) : Fin 4 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left, (toUnit (T ⊗ D.P.A) ≫ D.c α).left,
    (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left]

abbrev SecBT (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (famφT D T α) (DegPre.famε k))

abbrev PreU.SecGT (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ)))

def PreU.ExpT (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k)
    (f : ∀ α, SecBT D T k α) : Prop :=
  ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left), rG ≫ (snd T G).left = x ≫ (fstG I e G).left →
    rB ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (f α) rB z J = 0) ∧
      (gw (U.w e) x z (J (x ≫ (U.gt e).pG.left)) (fun _ => JG (x ≫ (fstG I e G).left))).val ^ k * sval σ rG z JG =
        ∑ α ∈ s, sval (f α) rB z J * (val ((U.gt e).t α) x z J).val

def PreU.Red (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ G) (g : GtPt D T) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (xe : Z ⟶ (thickObj R I e G).left),
    xe ≫ (fstG I e G).left = r ≫ x.left → xe ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
      ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) xe z J = val (g.s χ) r z J
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev Raw (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

def PreU.ExpF (U : PreU I D A G) (k : ℕ) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Raw D F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecGT (𝟙_ _) k) (f : Fin n → ∀ α, SecBT D (𝟙_ _) k α),
    (∀ i, U.ExpT (𝟙_ _) k (σ i) (f i)) ∧
    (∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
      rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t rA z JA =
          ∑ i, gs rA z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (σ i) rG z JG) ∧
    ∀ (α : D.X) (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
        sval (s α) rF z J = ∑ i, gs rF z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (f i α) rB z J

def PhiRaw (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (y : D.X) (g : GtPtF D F)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (s s' : Raw D F k) : Prop :=
  ∀ (α : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F y α g.b) (DegPre.deltaε k))), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + y)) (DegPre.famε k) (s' (α + y))
      (DegPre.famφ D F α) (DegPre.famε k) (s α) (DegPre.trPt D F g.b).left (DegPre.phiφ D F y α g.b) (DegPre.deltaε k) u

def CDVR (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] : Prop :=
  IsDiscreteValuationRing V ∧ IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V
end GlobalTheory.UU
end
end
