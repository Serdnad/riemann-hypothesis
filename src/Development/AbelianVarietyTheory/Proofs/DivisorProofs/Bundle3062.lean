module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjSwap

section Charts

variable {X Y Y' : Scheme.{0}}

def pullInv {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso B A) :
    LB.Iso A' B' where
  s p := (res (fun y hy => ⟨a.le _ hy.2, b.le _ hy.1⟩ :
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)))
    (pullU h _ (w.s (a.idx p.2, b.idx p.1))))⁻¹

theorem gm_pullInv {Z : Scheme.{0}} {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (b : ChartPull B' B h) (w : LB.Iso B A) (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullInv a b w).s p) =
      (gm (r ≫ h) z (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans
    (gm_pull r h z _ (show h (r z) ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) from ⟨a.le _ hz.2, b.le _ hz.1⟩) _)))

theorem pullInv_isGen {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    {w : LB.Iso B A} (hw : w.IsGen) : (pullInv a b w).IsGen := fun p q => unit_ext fun y hy => by
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((pullInv a b w).s p) =
        (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ := fun p hp =>
    (gm_pullInv a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) :=
    ⟨⟨a.le _ hy.1.2, b.le _ hy.1.1⟩, ⟨a.le _ hy.2.2, b.le _ hy.2.1⟩⟩
  have e := congrArg (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1))))
    (hw (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1))
  have e' : gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)) =
      gm h y (A.U (a.idx p.2) ⊓ A.U (a.idx q.2)) (A.g (a.idx p.2) (a.idx q.2)) *
        (gm h y (B.U (b.idx p.1) ⊓ B.U (b.idx q.1)) (B.g (b.idx p.1) (b.idx q.1)))⁻¹ *
        gm h y (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) (w.s (a.idx q.2, b.idx q.1)) :=
    (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B A h y (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1) hm) (gm_res h y _ hm _))))
  have d : gm (𝟙 Y') y ((LB.div B' A').U p ⊓ (LB.div B' A').U q) ((LB.div B' A').g p q) =
      gm (𝟙 Y') y (B'.U p.1 ⊓ B'.U q.1) (B'.g p.1 q.1) * (gm (𝟙 Y') y (A'.U p.2 ⊓ A'.U q.2) (A'.g p.2 q.2))⁻¹ :=
    gm_div A' B' (𝟙 Y') y p q hy
  refine (gm_res _ y _ hy _).trans ((val p hy.1).trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  rw [d, gm_res (𝟙 Y') y _ hy, val q hy.2, b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, e']
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem gm_gen_congr {M : LB X} (t : LB.Gen M) {r r' : Y ⟶ X} (hr : r = r') (y : Y) {i i' : M.ι} (hi : i = i') :
    gm r y (M.U i) (t.s i) = gm r' y (M.U i') (t.s i') := by
  subst hr hi; rfl

theorem gm_g_congr (L : LB X) (f : Y ⟶ X) (y : Y) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') :
    gm f y (L.U i ⊓ L.U j) (L.g i j) = gm f y (L.U i' ⊓ L.U j') (L.g i' j') := by
  subst hi hj; rfl

def chartPullPerm (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : K ≃ K) (hc : ∀ k, φ' k = h ≫ φ (e k)) (hε : ∀ k, ε (e k) = ε k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j k := j (e.symm k)
  le j y hy := Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy (e.symm k)
    rw [hc, Equiv.apply_symm_apply] at this
    exact this
  g y j j' hj hj' := by
    refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_ (gm_linComb L φ ε h y _ _
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj' (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)).symm)
    refine Fintype.prod_equiv e _ _ fun k => ?_
    simp only [hε, Category.id_comp, hc]
    exact congrArg (· ^ ε k) (gm_g_congr L _ y (congrArg j (e.symm_apply_apply k)).symm
      (congrArg j' (e.symm_apply_apply k)).symm)

end Charts

section Sums

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I = ∏ i ∈ I, x i := by
  have hnd : ((List.finRange n).filter (· ∈ I)).Nodup := (List.nodup_finRange n).filter _
  calc psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
        unfold psum
        generalize ((List.finRange n).filter (· ∈ I)) = l
        induction l with
        | nil => rfl
        | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]; rfl
    _ = ∏ i ∈ I, x i := by
        rw [← List.prod_toFinset x hnd]
        congr 1
        ext i
        simp

theorem psum_perm {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G))
    (π : Equiv.Perm (Fin n)) (hx : ∀ i, x' i = σ ≫ x (π i)) (I : Finset (Fin n)) :
    psum G x' I = σ ≫ psum G x (I.map π.toEmbedding) := by
  calc psum G x' I = ∏ i ∈ I, x' i := psum_eq_prod x' I
    _ = ∏ i ∈ I, σ ≫ x (π i) := by simp only [hx]
    _ = σ ≫ ∏ i ∈ I, x (π i) := (map_prod (preHom (G := G) σ) _ I).symm
    _ = σ ≫ ∏ i ∈ I.map π.toEmbedding, x i := by rw [Finset.prod_map]; rfl
    _ = σ ≫ psum G x (I.map π.toEmbedding) := by rw [psum_eq_prod]

end Sums

def swapIdx : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).finsetCongr.trans Equiv.ulift.symm)

theorem swapIdx_down (I : ULift.{0} (Finset (Fin 2))) :
    (swapIdx I).down = I.down.map (Equiv.swap (0 : Fin 2) 1).toEmbedding := rfl

end GlobalTheory.MumFam.AdjSwap

namespace GlobalTheory.MumFam


open AdjSwap in
theorem adj_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₁ a' a h' h := by
  intro R _ _ Q₁ Q₂ a a' h h' ⟨ha, ha', hc, hc', w, hw, hv⟩
  let σ : Q₂.B ⊗ Q₁.B ⟶ Q₁.B ⊗ Q₂.B := lift (snd Q₂.B Q₁.B) (fst Q₂.B Q₁.B)
  have hA : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] K.down).left =
      σ.left ≫ (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hB : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] K.down).left =
      σ.left ≫ (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hε : ∀ K : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - (swapIdx K).down.card)) = (-1) ^ (2 - K.down.card) :=
    fun K => by rw [swapIdx_down, Finset.card_map]
  let cA : ChartPull (cubeLB Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] Q₁.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L) σ.left :=
    chartPullPerm Q₁.M.L _ _ _ σ.left swapIdx hA hε
  let cB : ChartPull (cubeLB Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] Q₂.M.L)
      (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) σ.left :=
    chartPullPerm Q₂.M.L _ _ _ σ.left swapIdx hB hε
  refine ⟨ha', ha, hc', hc, pullInv cA cB w, pullInv_isGen cA cB hw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hp : (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left ≫ σ.left =
      (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left := by
    rw [← Over.comp_left]; congr 1; simp [σ]
  have key : adjVal (pullInv cA cB w) (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left z J₁ J₂ =
      (adjVal w (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left z J₂ J₁)⁻¹ := by
    let p' := (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left
    have m₁ := hJ₁.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left) p'
    have m₂ := hJ₂.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left) p'
    have e1 := gm_pullInv cA cB w p' z
      (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left),
        fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)) ⟨m₁, m₂⟩
    have i₁ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] k.down).left := fun k => by
      rw [hA, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have i₂ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] k.down).left := fun k => by
      rw [hB, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have e2 := gm_gen_congr w hp z (Prod.ext (funext fun k => congrArg J₂ (i₁ k)) (funext fun k => congrArg J₁ (i₂ k)) :
      ((cA.idx (fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)),
        cB.idx (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left))) :
          (LB.div (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L)
            (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)).ι) =
        (fun I => J₂ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] I.down).left),
          fun I => J₁ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left)))
    exact e1.trans (congrArg (·⁻¹) e2)
  have o := hv y' y z J₂ J₁ hJ₂ hJ₁
  rw [Q₂.tau_symm (h y') y z J₁ hJ₁, Q₁.tau_symm y' (h' y) z J₂ hJ₂] at o
  rw [key, o, inv_mul_cancel_left]

end GlobalTheory.MumFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_io : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  intro F _ N N' r W φ e wv hT y'
  obtain ⟨-, -, he_add, -, hc, hw0, -, hψ⟩ := hT
  refine ⟨fun j => hc y' j, fun χ' => ?_⟩
  simp only [NumD.io_s, NumD.io_b]
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  let P : N'.X → Fˣ := fun a => ∏ i, ∏ j, N.τ (e a i) (e a j) ^ W i j
  have hψ' : ∀ a, N'.ψ a * U 1 = U (N'.c a) * P a := fun a => Units.ext (by
    simp only [Units.val_mul, U, Units.val_mk0, P]; exact hψ a)
  have key : ∀ i j, N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j))) =
      N.τ (e (y' + χ') i) (e (y' + χ') j) / N.τ (e y' i) (e y' j) / N.τ (e χ' i) (e χ' j) := by
    intro i j
    rw [he_add y' χ' i, he_add y' χ' j, add_comm (e y' i), add_comm (e y' j)]
    have h1 := N.τ_add_left (e χ' i) (e y' i) (e χ' j + e y' j)
    rw [N.c_add] at h1
    have h2 := N.τ_add_right (e χ' i) (e χ' j) (e y' j)
    have h3 := N.τ_add_right (e y' i) (e χ' j) (e y' j)
    have h4 := N.τ_symm (e y' j) (e χ' i)
    replace h1 := congrArg Additive.ofMul h1
    replace h2 := congrArg Additive.ofMul h2
    replace h3 := congrArg Additive.ofMul h3
    replace h4 := congrArg Additive.ofMul h4
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h1 h2 h3 h4 ⊢
    linear_combination (norm := abel) h4 - h1 - h2 - h3
  have hQ : (∏ i, ∏ j, (N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j)))) ^ W i j : Fˣ) =
      P (y' + χ') / P y' / P χ' := by
    simp only [key, div_zpow, Finset.prod_div_distrib, P]
  rw [hQ, hU, hU, hU, hU]
  have hS := hψ' (y' + χ')
  rw [N'.c_add y' χ', mul_comm (N'.c y')] at hS
  have hy := hψ' y'
  have hx := hψ' χ'
  have E : N'.τ y' χ' * U (N'.c χ') * U (N'.c y') = P (y' + χ') / P y' / P χ' * U (N'.c χ' * N'.c y') * U 1 := by
    simp only [NumD.τ]
    replace hS := congrArg Additive.ofMul hS
    replace hy := congrArg Additive.ofMul hy
    replace hx := congrArg Additive.ofMul hx
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at hS hy hx ⊢
    linear_combination (norm := abel) hS - hy - hx
  have := congrArg Units.val E
  simpa only [Units.val_mul] using this

end GlobalTheory.Mum.TensTor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensPsiCoord

open GlobalTheory.PsiTauCoordRel GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  intro R _ _ _ Q D' r W pr xe hT y k hk x hx
  obtain ⟨-, -, -, w, -, hpsi⟩ := hT
  haveI : IsProper D'.P.A.hom := D'.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom
  have E := hpsi y ξ J J' hJ hJ'

  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨u₁, g₁⟩ := val_psi_chart D' ξ hJ' hc' y j hj (h trivial)
  have eP := gm_genVal ξ (D'.psi y) j h

  obtain ⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val =
      GlobalTheory.PeriodBalance.cst ξ u := by
    refine GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _
    · obtain ⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by
        obtain ⟨⟨a, b⟩, c⟩ := I
        fin_cases c <;> exact ⟨_, rfl⟩
      have := hc ((D'.c y).left ≫ tensφ pr I) (by
        rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
      rw [← Category.assoc] at this
      exact this
    · exact hc' _ (Over.w _)

  have hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J =
      GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v := by
    intro i j
    obtain ⟨u, -, hu⟩ := hk i j
    obtain ⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by
      refine val_int ξ hc u (𝟙 _) fun l => ?_
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B,
          GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by
        fin_cases l <;> exact ⟨_, rfl⟩
      rw [Category.id_comp, hq, Over.w q]; rfl
    refine ⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩
    · have := GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)
      rw [show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp] at this
      exact Units.ext this
    · rw [toUnit_left, ← Category.comp_id (jK R)]; exact hv
  choose v hv using hv
  have hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) =
      GlobalTheory.TauShift.cK ξ z := fun z => Units.ext rfl
  refine ⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩
  change GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _
  have eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) =
      GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h) := Units.ext eP
  have e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂ :=
    Units.ext e₂
  have G := g₁.symm.trans (E.trans (by rw [e₂']))
  rw [eP'] at G
  simp only [hv] at G
  simp only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢
  have G' := congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G
  simp only [inv_mul_cancel_left] at G'
  rw [G']
  ac_rfl

end GlobalTheory.TensPsiCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRos

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def PV (W : Matrix (Fin r) (Fin r) ℤ) (e : N'.X → Fin r → N.X) (χ' : N'.X) (vs : Fin r → N.Gt) : F :=
  ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
        N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F)

theorem gtRelV_iff (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) :
    GtRelV W φ e wv v' vs ↔ (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
      (v'.s χ' : F) * wv (N'.c χ') * wv v'.b = PV W e χ' vs * wv (N'.c χ' * v'.b) * wv 1 := Iff.rfl

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def tensJ (T : Tens D D' W) (ν : NumOf D F N) (y : Sp F ⟶ D'.P.A.left) :
    (LB.LinComb D.P.L (tensφ T.pr) (tensε W)).ι :=
  fun k => ν.J (y ≫ tensφ T.pr k)

def RosVT (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (f g : D'.P.A ⟶ D'.P.A) (ρ : N'.A → N'.A → F) :
    Prop :=
  ∃ u : LB.Gen (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) (rosatiφ D'.P.A f g) rosatiε), u.IsGen ∧
    LB.Gen.Corr (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ _ _
      (LB.pullGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ u (zero2 D'.P.A))
      (LB.oneGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W))) ∧
    ∀ b b', ρ b b' = vF u (lift (ν'.eA b) (ν'.eA b')).left (tensJ T ν)

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] [Module O D'.X] (o : D'.OAct O)
    (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (j : Fin r) :
    GlobalTheory.Mum.TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) j = ∏ k, GlobalTheory.Mum.TensTor.cmp T ν ν' b k ^ ρ x j k := by
  letI := D.P.isAb.comm
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := MonObj.comp_one _
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have e : ν'.eA (GlobalTheory.Relabel.actV ν' o.onB x b) ≫ T.pr j = P (∏ k, T.pr k ^ ρ x j k) := by
    rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x j]; rfl
  rw [GlobalTheory.Mum.TensTor.cmp, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  rfl

theorem c_actV {R : Type} [CommRing R] [IsDomain R] {D' : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N' : NumD F} (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (a : O) (χ : N'.X) :
    GlobalTheory.Relabel.actV ν' o.onB a (N'.c χ) = N'.c (ν'.eX.symm (a • ν'.eX χ)) := by
  apply ν'.eA.injective
  rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, ν'.c_eq, ν'.c_eq, AddEquiv.apply_symm_apply]
  show (toUnit _ ≫ D'.c _) ≫ _ = toUnit _ ≫ D'.c _
  rw [o.c_lin, Category.assoc]

end GlobalTheory.Mum.TensRos
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

theorem famTw_add_f : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  intro R _ _ D N σ s s' s'' h α j
  have e : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => (h α j).trans (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α j).symm
  subst e
  show ((GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N (s + s') :
    Fam D (TwF σ) N).s α).f j = _
  rw [map_add (f := _)]
  rfl

end GlobalTheory.Mum.Conj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem famTw_isSmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N),
    Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  intro R _ _ D N σ c s s' h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff] at h
  subst h
  intro α j
  have e := map_smulₛₗ (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N) c s
  exact congrArg (fun q : Fam D (TwF σ) N => (q.s α).f j) e

end GlobalTheory.Mum.Conj
end
