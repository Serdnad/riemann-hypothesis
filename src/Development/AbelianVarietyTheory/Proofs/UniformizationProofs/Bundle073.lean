module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ToChart

local instance (priority := high) grpObjChartThick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e))

theorem gm_res_pull {X Y : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU g U a)) = gm g y U a :=
  (gm_res _ y h hy _).trans ((gm_pull (𝟙 Y) g y U (h hy) a).trans (by rw [Category.id_comp]))

theorem cub_alg' {M : Type} [CommGroup M] {C C' a b c d e g h k : M} (H : C * b * c * d * k = a * e * g * h * C') :
    C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C' := by
  apply Additive.ofMul.injective
  have H' := congrArg Additive.ofMul H
  simp only [ofMul_mul, ofMul_inv] at H' ⊢
  linear_combination (norm := abel) H'

theorem cube_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {T : Over S} {T' : Over S'} (β : (T' ⟶ G') →* (T ⟶ G)) (x : Fin 3 → (T' ⟶ G')) (k : thK) :
    (lift (β (x 0)) (lift (β (x 1)) (β (x 2)))).left ≫ thφ G (x3 G) k = (β (psum G' x k.down)).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift (β (x 0)) (lift (β (x 1)) (β (x 2))))) (x3 G) k.down).trans
    ((congrArg (fun q => psum G q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])).trans
      (psum_hom β x k.down).symm))

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)

def fstHom (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    toBase_mul_pullback G (thick R I e) T x y

variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def projHom (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) fun x y => by
    have := g.q_hom
    have h : ∀ a : T ⟶ thickObj R I e G, (Over.map (thick R I e)).map a ≫ g.pG = fstHom I e D.P.A T (a ≫ g.q) :=
      fun a => by rw [← Category.assoc, ← Functor.map_comp]; rfl
    rw [h, h, h, MonObj.mul_comp, map_mul]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)

theorem w_compat (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.P.L.pull (U.gt (e + 1)).pG.left).U p.1 ⊓
      (U.P.L.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2) :
    res h₁ (pullU (thickMap R I e G) _ ((U.w (e + 1)).s p)) = res h₂ ((U.w e).s p) := by
  refine unit_ext fun y hy => ?_
  have := U.w_compat e _ (𝟙 _) y (p.1 PUnit.unit) (p.2 PUnit.unit) (mem_pull.1 (h₂ hy).1) (mem_pull.1 (h₂ hy).2)
  rw [Category.id_comp] at this
  exact (gm_res_pull _ h₁ hy _).trans (this.trans (gm_res _ y h₂ hy _).symm)

theorem w_rig (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (U.P.L.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U p.1) :
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((U.w e).s p)) *
      res h₂ (pullU (thick R I e) _ (U.P.L.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.rig.s p.1)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec G, eSec (thickObj R I e G) ≫ (fstG I e G).left] (fun _ => p.2 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₂ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).2 PUnit.unit⟩)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec D.P.A, eSec (thickObj R I e G) ≫ (U.gt e).pG.left] (fun _ => p.1 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₃ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).1 PUnit.unit⟩)
  have H := (U.w_vals e (𝟙_ _) y JG J hJG hJ _ (fun _ => rfl)).1
  have o : (1 : 𝟙_ _ ⟶ thickObj R I e G).left = eSec (thickObj R I e G) :=
    (one_left _ _).trans (Category.id_comp _)
  have t : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).hom ≫ thick R I e = thick R I e := Category.id_comp _
  rw [o, t] at H
  have a := val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (thick R I e) y J p.1
    (fun _ => eB 0)
  have b := val_of (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (thick R I e) y JG p.2
    (fun _ => eG 0)
  have c := congrArg₂ (fun j k => gw (U.w e) (eSec (thickObj R I e G)) y j (fun _ => k)) (eB 1) (eG 1)
  refine (map_mul _ _ _).trans (Eq.trans ?_ (gm_res_pull _ h₃ hy _).symm)
  refine (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res_pull _ h₂ hy _)).trans ?_
  exact (a.symm.trans (H.trans (congrArg₂ (· * ·) c b))).symm

theorem w_even (e : ℕ) (jS : Fin 2 → U.P.L.L.ι) (jT : Fin 2 → D.P.L.ι)
    (cS : LB.Coh U.P.L.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS)
    (cT : LB.Coh D.P.L
      (fun k => (U.gt e).pG.left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) jT)
    (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.P.L (K := Fin 2)
        ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.P.L.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS) :
      res h₁ (pullU (U.gt e).pG.left _ (D.sym.s jT)) *
        res h₂ ((U.w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((U.w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (U.P.sym.s jS)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jS cS (fun k => Set.mem_iInter.1 (h₄ hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jT cT (fun k => Set.mem_iInter.1 (h₁ hy) k)
  have H := (U.w_vals e _ y JG J hJG hJ _ (fun _ => rfl)).2.1 (𝟙 _)
  have o : ((𝟙 (thickObj R I e G))⁻¹).left = (ι[thickObj R I e G]).left := by rw [Hom.inv_def, Category.id_comp]
  have iG : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    (congrArg (fun q => q.left) (map_inv (fstHom I e G _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[G]).left) (Category.id_comp (fstG I e G).left))
  have iB : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ (ι[D.P.A]).left :=
    (congrArg (fun q => q.left) (map_inv (projHom (U.gt e) _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[D.P.A]).left) (Category.id_comp (U.gt e).pG.left))
  have g₀ : JG ((fstG I e G).left ≫ (ι[G]).left) = jS 0 := eG 0
  have g₁ : JG (fstG I e G).left = jS 1 := (congrArg JG (Category.comp_id _).symm).trans (eG 1)
  have b₀ : J ((U.gt e).pG.left ≫ (ι[D.P.A]).left) = jT 0 := eB 0
  have b₁ : J (U.gt e).pG.left = jT 1 := (congrArg J (Category.comp_id _).symm).trans (eB 1)
  rw [iG, iB, o, g₀, b₀, Over.id_left, Category.id_comp, Category.id_comp, g₁, b₁, val_of _ _ _ _ jT eB,
    val_of _ _ _ _ jS eG] at H
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  exact (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res _ y h₂ hy _)).trans
    (H.trans (congrArg₂ (· * ·) (gm_res_pull _ h₃ hy _) (gm_res_pull _ h₄ hy _)).symm)

theorem w_cub (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → U.P.L.L.ι) (jM : thK → D.P.L.ι)
    (cL : LB.Coh U.P.L.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL)
    (cM : LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ≫
          thφ D.P.A (x3 D.P.A) k) jM)
    (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ⁻¹ᵁ
            (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G U.P.L.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓
          (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL k))) :
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((U.w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (U.P.c.t.s jL)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jL cL (fun k => Set.mem_iInter.1 (hG hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 (hB hy) k)
  obtain ⟨h, hh⟩ : ∃ h : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk y)ˣ, ∀ q,
      h q = gw (U.w e) q y (J (q ≫ (U.gt e).pG.left)) (fun _ => JG (q ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  have H := (U.w_vals e T y JG J hJG hJ (fun a => h a.left) (fun _ => hh _)).2.2 (x 0) (x 1) (x 2)
  have P := prod_cub (x 0) (x 1) (x 2) h
  have Q : ∀ k : thK, gm (𝟙 T.left) y V (res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
      ((U.w e).s (fun _ => jM k, fun _ => jL k)))) =
      h ((lift (x 0) (lift (x 1) (x 2))).left ≫ thφ (thickObj R I e G) (x3 _) k) := fun k => by
    have g : JG ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) = jL k :=
      (congrArg JG (cube_left (fstHom I e G T) x k).symm).trans (eG k)
    have b : J ((psum (thickObj R I e G) x k.down).left ≫ (U.gt e).pG.left) = jM k :=
      (congrArg J (cube_left (projHom (U.gt e) T) x k).symm).trans (eB k)
    refine (gm_res_pull _ (hw k) hy _).trans (Eq.trans ?_ (congrArg h (cube_left (MonoidHom.id _) x k)).symm)
    exact ((hh _).trans (congrArg₂ (fun j l => gw (U.w e) (psum (thickObj R I e G) x k.down).left y j (fun _ => l))
      b g)).symm
  have a := val_of (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t _ y J jM eB
  have b := val_of (L := U.P.L.L) (φ := thφ G (x3 G)) (ε := thε) U.P.c.t _ y JG jL eG
  refine (gm_res_pull _ hB hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ thε k) (Q k)))).trans P) (gm_res_pull _ hG hy _))).symm)
  exact a.symm.trans ((cub_alg' H).trans (congrArg₂ (· * ·) rfl b))

theorem exists_match : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G), ∃ U' : UnifPre I D A G, Match U U' :=
  fun _ _ _ _ _ _ _ _ _ U =>
    ⟨{ smooth := U.semi.smooth
       separated := U.semi.separated
       gen := U.gen
       gen_hom := U.gen_hom
       LG := U.P.L
       cubG := U.P.c
       symG := U.P.sym
       symG_gen := U.P.sym_gen
       symG_rig := U.P.sym_rig
       ext := ⟨U.wA, U.wA_gen⟩
       gt := U.gt
       gt_q := U.gt_q
       gt_t := U.gt_t
       w := U.w
       w_gen := U.w_gen
       w_rig := w_rig U
       w_even := w_even U
       w_cub := w_cub U
       w_compat := w_compat U }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩⟩

end GlobalTheory.UU.ToChart
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.PsiScalUnit

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ w * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

variable {V : Type} [CommRing V] [IsDomain V]

def ev (z : (TK V).left) : FractionRing V →+* (TK V).left.presheaf.stalk z :=
  ((TK V).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem ev_eq (z : (TK V).left) (k : FractionRing V) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (TK V) : TK V ⟶ TK V).left k) = ev z k := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem ev_unit (z : (TK V).left) (w : Γ(Spec (CommRingCat.of V), ⊤)ˣ) :
    ∃ u : Vˣ, (gm (jK V) z ⊤ w).val = ev z (algebraMap V (FractionRing V) u.val) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom w, ?_⟩
  rw [← gs_unit _ z ⊤ trivial, gs_eq _ z ⊤ trivial]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at e
  exact congrArg ((TK V).left.presheaf.germ ⊤ z trivial).hom e.symm

theorem c_left (D : DegPre V) (χ : D.X) : (D.c χ).left = (DVR.cP D (𝟙_ _) χ).left := by
  rw [DVR.cP, toUnit_unit, Category.id_comp]

theorem exists_setup (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) :
    ∃ (z : (TK V).left) (J : _), Good D.P.L z J ∧ ∀ χ, val (D.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (a χ) * val (ga χ) (toUnit (TK V)).left z J := by
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose J hJ using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, J, hJ, fun χ => Units.ext ?_⟩
  exact ((h χ).2 (TK V) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl)

theorem ev_inj (z : (TK V).left) : Function.Injective (ev z) := (ev z).injective

theorem cub_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hB : D.TauBimult) (x y w : D.X) :
    ∃ u : Vˣ, (a (x + y + w) * a x * a y * a w).val =
      algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + w) * a (y + w)).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK V)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 x y w)) (𝟙 _) z J =
      cubV D.cub z J (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w) := by
    refine (val_cub D.cub (𝟙 (TK V)) hJ (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w)).trans ?_
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB x y w) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [vc, vτ, vτ, vτ, vρ] at e
  simp only [hψ] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have p₁ := prod_cub (DVR.cP D (𝟙_ _) x) (DVR.cP D _ y) (DVR.cP D _ w) f
      have q : eSec D.P.A = (1 : 𝟙_ _ ⟶ D.P.A).left := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
      refine Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ rfl p₁).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c_left, DVR.cPoint_add, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y)).1 (h (x + w)).1) (h (y + w)).1)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y + w)).1 (h x).1) (h y).1) (h w).1)
      D.rig_gen) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε _ D.cub.isGen
        (lift (DVR.cP D (𝟙_ _) x) (lift (DVR.cP D (𝟙_ _) y) (DVR.cP D (𝟙_ _) w))).left))
  have e₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)).symm.trans
    ((hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) rfl)) rfl))
      (val_cub D.cub (toUnit (TK V)) hJ _ _ _)))))
  rw [DVR.comp_cP, DVR.comp_cP, DVR.comp_cP] at e₂
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (x + y + w) * a x * a y * a w) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a (x + y) * a (x + w) * a (y + w)) := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem even_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hE : D.PsiEven) (x : D.X) :
    ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE x) (𝟙 _))
  rw [hψ, hψ, Category.id_comp] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have q : (D.c x).left ≫ (ι[D.P.A]).left = (D.c (-x)).left := by
        have h0 : DVR.cP D (𝟙_ _) 0 = 1 := by simpa using DVR.cPoint_nsmul D (𝟙_ _) 0 x
        have h1 := DVR.cPoint_add D (𝟙_ _) (-x) x
        rw [neg_add_cancel, h0] at h1
        rw [c_left, c_left, eq_inv_of_mul_eq_one_left h1.symm, ← Over.comp_left]
        rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (h x).1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (-x)).1 (DVR.pullGen_isGen D.P.L _ _ _ D.sym_gen (D.c x).left))
  have e₂ := (hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (-x)) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a x) := by
    have e' : Units.map (ev z).toMonoidHom (a (-x)) * val (ga (-x)) (toUnit (TK V)).left z J *
        val D.sym ((toUnit (TK V)).left ≫ (D.c x).left) z J =
        Units.map (ev z).toMonoidHom (a x) * val (ga x) (toUnit (TK V)).left z J := e
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e'
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) :=
  fun _ _ _ _ D ga a h => ⟨cub_part D ga a h, even_part D ga a h⟩

end GlobalTheory.PsiScalUnit
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU

theorem exists_lift_unit_tensor {S Z : Scheme.{0}} (X : Over S) (q : Z ⟶ X.left) :
    ∃ r : Z ⟶ (𝟙_ (Over S) ⊗ X).left, r ≫ (snd _ X).left = q ∧ r ≫ (fst _ X).left = q ≫ X.hom := by
  refine ⟨q ≫ (λ_ X).inv.left, ?_, ?_⟩
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_snd, Over.id_left, Category.comp_id]
  · rw [Category.assoc, ← Over.comp_left, leftUnitor_inv_fst]
    rfl

theorem expandsAt_of_expT : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → U.ExpT (𝟙_ _) k σ' f' → ∀ e, U'.ExpandsAt e k σ f := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  dsimp only at hL hgt hw
  subst hL hgt
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hσ
  obtain ⟨S, hS⟩ := hE e
  refine DVR.expandsAt_of_val U' e k σ f S fun y J hJ => ?_
  obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (fstG I e G).left
  obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (U'.gt e).pG.left
  have hc : (U'.gt e).pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
    (Over.w (U'.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := hS _ (𝟙 _) rG rB (hG₁.trans (Category.id_comp _).symm) (hB₁.trans (Category.id_comp _).symm)
    (hB₂.trans (hc.trans hG₂.symm)) y
  have hf : ∀ α, sval (f' α) rB y J = sval (f α) (DVR.pGl U' e) y J := fun α => by
    rw [hB α _ rB y J hJ, hB₁]
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · choose JG hJG using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U'.LG.isLB (ψ y)
    exact (hf α).symm.trans ((H JG J hJG hJ).1 α hα)
  · obtain ⟨JG, hJG, eJ⟩ := exists_good U'.LG.L U'.LG.isLB y (fun _ : PUnit => (fstG I e G).left) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    have e₀ : JG (fstG I e G).left = jL := eJ PUnit.unit
    have H₂ := (H JG J hJG hJ).2
    have hs : sval σ' rG y JG = DVR.sv U' k σ (DVR.fGl I G e) y jL := by
      rw [hG _ rG y JG hJG, hG₁]
      exact sval_of σ _ y JG (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact e₀)
    simp only [Category.id_comp, e₀, hs, hf] at H₂
    rw [Units.val_pow_eq_pow_val]
    exact H₂

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem expT_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : H0 U'.LG.L k) (σ₀ : H0 U.P.L.L k) (σ' : U.SecGT (𝟙_ _) k) (f) (f'), HEq σ σ₀ → SameG σ₀ σ' → SameB f f' → (∀ e, U'.ExpandsAt e k σ f) → U.ExpT (𝟙_ _) k σ' f' := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ σ' f f' hσ hG hB hE e
  obtain ⟨S, hS⟩ := ReciprocityTheory.ChartRestriction.G.DVR.expandsAt_val U' e k σ f (hE e)
  refine ⟨S, fun Z x rG rB h1 h2 _ z JG J hJG hJ => ?_⟩
  obtain ⟨h₀, h₁⟩ := hS Z x z J hJ
  clear hS hE
  obtain ⟨-, hL, -, -, hgt, hw⟩ := hM
  cases U'
  dsimp only at hL hgt hw
  subst hL hgt
  cases hw
  cases hσ
  have eB : ∀ α, sval (f' α) rB z J = sval (f α) (x ≫ (U.gt e).pG.left) z J := fun α => by
    rw [hB α Z rB z J hJ, h2]
  refine ⟨fun α hα => (eB α).trans (h₀ α hα), ?_⟩
  have H := h₁ (JG (x ≫ (fstG I e G).left)) (hJG (x ≫ (fstG I e G).left))
  rw [hG Z rG z JG hJG, h1, Finset.sum_congr rfl fun α _ => congrArg (· * _) (eB α)]
  refine Eq.trans ?_ H
  rw [Units.val_pow_eq_pow_val, sval_of σ₀ _ z JG (fun _ => JG (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
  rfl

end GlobalTheory.UU
end
