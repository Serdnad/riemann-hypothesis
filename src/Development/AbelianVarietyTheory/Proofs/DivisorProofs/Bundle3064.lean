module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.AdjComp

section Iso

variable {X : Scheme.{0}}

theorem gm_iso {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (i j : B.ι × A.ι) (hi : f z ∈ B.U i.1 ⊓ A.U i.2) (hj : f z ∈ B.U j.1 ⊓ A.U j.2) :
    gm f z (B.U i.1 ⊓ A.U i.2) (w.s i) =
      gm f z (B.U i.1 ⊓ B.U j.1) (B.g i.1 j.1) * (gm f z (A.U i.2 ⊓ A.U j.2) (A.g i.2 j.2))⁻¹ *
        gm f z (B.U j.1 ⊓ A.U j.2) (w.s j) := by
  have hm : f z ∈ B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2) := ⟨hi, hj⟩
  have e := congrArg (gm f z (B.U i.1 ⊓ A.U i.2 ⊓ (B.U j.1 ⊓ A.U j.2))) (hw i j)
  exact (gm_res f z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B f z i j hm) (gm_res f z _ hm _))))

variable {A B C : LB X}

theorem exists_comp (hA : A.IsLB) (hB : B.IsLB) (hC : C.IsLB) (w₁ : LB.Iso A B) (hw₁ : w₁.IsGen)
    (w₂ : LB.Iso B C) (hw₂ : w₂.IsGen) :
    ∃ w : LB.Iso A C, w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (r : C.ι) (p : B.ι) (q : A.ι),
      f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z (C.U r ⊓ A.U q) (w.s (r, q)) =
        gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
  have glue : ∀ (r : C.ι) (q : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U q)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z)
      (p : B.ι), f z ∈ C.U r → f z ∈ B.U p → f z ∈ A.U q →
      gm f z _ s = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) := by
    intro r q
    let W : B.ι → X.Opens := fun p => C.U r ⊓ A.U q ⊓ B.U p
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U q := fun p => inf_le_left
    have l₂ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ B.U p ⊓ A.U q := fun p x hx => ⟨hx.2, hx.1.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₂ p) (w₂.s (r, p)) * res (l₁ p) (w₁.s (p, q))
    have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : B.ι) (hz : f z ∈ W p),
        gm f z (W p) (u p) = gm f z (C.U r ⊓ B.U p) (w₂.s (r, p)) * gm f z (B.U p ⊓ A.U q) (w₁.s (p, q)) :=
      fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₂ p) hz _) (gm_res f z (l₁ p) hz _))
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩) u (fun p p' x hx => by
        rw [hu _ (𝟙 X) x p hx.1, hu _ (𝟙 X) x p' hx.2]
        have a₂ := gm_iso hw₂ (𝟙 X) x (r, p) (r, p') ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩
        have a₁ := gm_iso hw₁ (𝟙 X) x (p, q) (p', q) ⟨hx.1.2, hx.1.1.2⟩ ⟨hx.2.2, hx.2.1.2⟩
        rw [a₂, a₁, gm_self hC (𝟙 X) x hx.1.1.1, gm_self hA (𝟙 X) x hx.1.1.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z f z p hr hp hq => ?_⟩
    have hy : f z ∈ W p := ⟨⟨hr, hq⟩, hp⟩
    exact (gm_res f z (l₀ p) hy s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hu Z f z p hy))
  choose s hs using glue
  refine ⟨⟨fun rq => s rq.1 rq.2⟩, fun i j => unit_ext fun x hx => ?_, fun Z f z r p q hr hp hq => hs r q Z f z p hr hp hq⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have e₁ := hs i.1 i.2 _ (𝟙 X) x p hx.1.1 hp hx.1.2
  have e₂ := hs j.1 j.2 _ (𝟙 X) x p hx.2.1 hp hx.2.2
  have a₂ := gm_iso hw₂ (𝟙 X) x (i.1, p) (j.1, p) ⟨hx.1.1, hp⟩ ⟨hx.2.1, hp⟩
  have a₁ := gm_iso hw₁ (𝟙 X) x (p, i.2) (p, j.2) ⟨hp, hx.1.2⟩ ⟨hp, hx.2.2⟩
  refine (gm_res (𝟙 X) x _ hx _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A C (𝟙 X) x i j hx) ((gm_res (𝟙 X) x _ hx _).trans e₂)).trans ?_
  rw [a₂, a₁, gm_self hB (𝟙 X) x hp]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

end Iso

section Pull

variable {Y Y' : Scheme.{0}} {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y}

theorem pullIso_le (a : ChartPull A' A h) (b : ChartPull B' B h) (p : B'.ι × A'.ι) :
    B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (pullIso_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_pullIso (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y')
    (z : Z) (p : B'.ι × A'.ι) (hp : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullIso a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (pullIso_le a b p) hp _).trans (gm_pull r h z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (pullIso_le a b p hp) _)

theorem pullIso_isGen (a : ChartPull A' A h) (b : ChartPull B' B h) {w : LB.Iso A B} (hw : w.IsGen) :
    (pullIso a b w).IsGen := fun p q => unit_ext fun y hy => by
  have hp : (𝟙 Y' ≫ h) y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) := ⟨b.le _ hy.1.1, a.le _ hy.1.2⟩
  have hq : (𝟙 Y' ≫ h) y ∈ B.U (b.idx q.1) ⊓ A.U (a.idx q.2) := ⟨b.le _ hy.2.1, a.le _ hy.2.2⟩
  have l := gm_iso hw (𝟙 Y' ≫ h) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hp hq
  have e₁ := (gm_res (𝟙 Y') y inf_le_left hy _).trans (gm_pullIso a b w (𝟙 Y') y p hy.1)
  have e₂ := (gm_res (𝟙 Y') y inf_le_right hy _).trans (gm_pullIso a b w (𝟙 Y') y q hy.2)
  refine e₁.trans (l.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  refine (congrArg₂ (· * ·) (gm_div A' B' (𝟙 Y') y p q hy) e₂).trans ?_
  rw [b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, Category.id_comp]

end Pull

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam.AdjComp

theorem psum_left_pull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) (I : ULift (Finset (Fin n))) :
    (psum G x' I.down).left = m.left ≫ (psum G x I.down).left := by
  obtain rfl : x' = fun i => m ≫ x i := funext hx
  rw [← Over.comp_left, comp_psum]

def cubePull {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (L : LB G.left) (m : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (hx : ∀ i, x' i = m ≫ x i) :
    ChartPull (cubeLB G x' L) (cubeLB G x L) m.left :=
  chartPullSame L _ _ _ m.left (psum_left_pull m x x' hx)

theorem adjVal_of {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) (j₁ : ULift (Finset (Fin 2)) → L₁.ι)
    (j₂ : ULift (Finset (Fin 2)) → L₂.ι) (h₁ : ∀ I, J₁ (p ≫ (psum G₁ x₁ I.down).left) = j₁ I)
    (h₂ : ∀ I, J₂ (p ≫ (psum G₂ x₂ I.down).left) = j₂ I) :
    adjVal w p z J₁ J₂ = gm p z ((cubeLB G₁ x₁ L₁).U j₁ ⊓ (cubeLB G₂ x₂ L₂).U j₂) (w.s (j₁, j₂)) := by
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₁ (p ≫ (psum G₁ x₁ I.down).left)) = j₁ := funext h₁
  obtain rfl : (fun I : ULift (Finset (Fin 2)) => J₂ (p ≫ (psum G₂ x₂ I.down).left)) = j₂ := funext h₂
  rfl

end GlobalTheory.MumFam.AdjComp

namespace GlobalTheory.MumFam


open AdjComp in
theorem Adj.comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ Q₃ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) (b : Q₂.B ⟶ Q₃.B) (b' : Q₃.B ⟶ Q₂.B) (k : Q₂.X →+ Q₃.X)
    (k' : Q₃.X →+ Q₂.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₃ b b' k k' →
      Adj Q₁ Q₃ (a ≫ b) (b' ≫ a') (k.comp h) (h'.comp k') := by
  intro R _ _ Q₁ Q₂ Q₃ a a' h h' b b' k k' H₁ H₂
  obtain ⟨ma, ma', ca, ca', w₁₂, g₁₂, V₁₂⟩ := H₁
  obtain ⟨mb, mb', cb, cb', w₂₃, g₂₃, V₂₃⟩ := H₂
  let m₁ : Q₁.B ⊗ Q₃.B ⟶ Q₂.B ⊗ Q₃.B := lift (fst _ _ ≫ a) (snd _ _)
  let m₂ : Q₁.B ⊗ Q₃.B ⟶ Q₁.B ⊗ Q₂.B := lift (fst _ _) (snd _ _ ≫ b')
  have xA : ∀ i, (![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B ≫ b, snd Q₂.B Q₃.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₁ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₁ ≫ (![fst Q₂.B Q₃.B, snd Q₂.B Q₃.B ≫ b'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₁]
  have xB₂ : ∀ i, (![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cA := cubePull Q₃.M.L m₁ _ _ xA
  let cB₁ := cubePull Q₂.M.L m₁ _ _ xB₁
  let cB₂ := cubePull Q₂.M.L m₂ _ _ xB₂
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] Q₃.M.L).IsLB := DVR.linComb_isLB _ Q₃.M.isLB _ _
  have lB : (cubeLB Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC (pullIso cA cB₁ w₂₃) (pullIso_isGen cA cB₁ g₂₃)
    (pullIso cB₂ cC w₁₂) (pullIso_isGen cB₂ cC g₁₂)
  refine ⟨inferInstance, inferInstance, fun y => ?_, fun y => ?_, w, gw, fun y y' z J₁ J₃ hJ₁ hJ₃ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb, ca, Category.assoc]
  · rw [AddMonoidHom.comp_apply, ca', cb', Category.assoc]
  · obtain ⟨J₂, hJ₂⟩ := GlobalTheory.ChartCmp.CarryCalc.exists_good' Q₂.M.isLB z
    have e₂₃ := V₂₃ (h y) y' z J₂ J₃ hJ₂ hJ₃
    have e₁₂ := V₁₂ y (k' y') z J₁ J₂ hJ₁ hJ₂
    have hP₂₃ : (lift (toUnit (TK R) ≫ Q₂.c (h y)) (toUnit (TK R) ≫ Q₃.c y')).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₁.left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, ca, Category.assoc]
    have hP₁₂ : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c (k' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, cb', Category.assoc]
    rw [hP₂₃] at e₂₃
    rw [hP₁₂] at e₁₂
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₃.c y')).left = P at e₂₃ e₁₂ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₃.B, snd Q₁.B Q₃.B ≫ b' ≫ a'] I.down).left) P
    have mB := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₃.B ≫ a, snd Q₁.B Q₃.B ≫ b'] I.down).left) P
    have mA := Good.mem hJ₃ (fun I : ULift (Finset (Fin 2)) => (psum Q₃.B ![fst Q₁.B Q₃.B ≫ a ≫ b, snd Q₁.B Q₃.B] I.down).left) P
    have K : adjVal w P z J₁ J₃ = adjVal w₂₃ (P ≫ m₁.left) z J₂ J₃ * adjVal w₁₂ (P ≫ m₂.left) z J₁ J₂ := by
      refine ((adjVal_of w P z J₁ J₃ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB₂ cC w₁₂ P z (_, _) ⟨mC, mB⟩) (gm_pullIso cA cB₁ w₂₃ P z (_, _) ⟨mB, mA⟩)))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂₃ (P ≫ m₁.left) z J₂ J₃ _ _ (fun I => ?_) (fun I => ?_)).symm
        (adjVal_of w₁₂ (P ≫ m₂.left) z J₁ J₂ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xB₁ I]
      · show J₃ _ = J₃ _
        rw [Category.assoc, ← psum_left_pull m₁ _ _ xA I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₂ _ = J₂ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB₂ I]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e₂₃, e₁₂, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

section Helpers
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_zpow (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => n * ε k)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨GeneratorPullback.powGen L φ ε t m, DVR.powGen_isGen _ _ _ _ ht m,
      fun Z r z J _ => (DVR.val_pow t m r z J).trans (zpow_natCast _ _).symm⟩
  · obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => -(m : ℤ) * ε k) (fun U _ h => by
        refine Finset.prod_congr rfl fun k _ => ?_
        show _ = h (φ k) ^ (-(m : ℤ) * ε k)
        rw [neg_mul]) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t m))
        (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht m))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv Z r z J hJ, val_inv, DVR.val_pow, zpow_neg, zpow_natCast]

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Helpers

section Rows
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem comp_tensφ' {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = GlobalTheory.PolDeg.lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem matAct_zero (T : Tens D D' W) : GlobalTheory.TensAct.matAct T 0 = 1 := by
  have h := GlobalTheory.TensAct.matAct_add T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem four_eq (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A)
    (hf : f = GlobalTheory.TensAct.matAct T A) (a : Fin 4) :
    (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] :
      Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) a =
      (GlobalTheory.TensAct.matAct T ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a)).left := by
  subst hf
  fin_cases a
  · show (padd D'.P.A (𝟙 _) _).left = (GlobalTheory.TensAct.matAct T (1 + A)).left
    rw [GlobalTheory.TensAct.matAct_add, GlobalTheory.TensAct.matAct_one]; rfl
  · show 𝟙 D'.P.A.left = (GlobalTheory.TensAct.matAct T 1).left
    rw [GlobalTheory.TensAct.matAct_one]; rfl
  · rfl
  · show (toUnit D'.P.A ≫ η[D'.P.A]).left = (GlobalTheory.TensAct.matAct T 0).left
    rw [matAct_zero]; rfl

theorem sum_one_smul {X : Type} [AddCommGroup X] (v : Fin r → X) (i : Fin r) :
    ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • v k = v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem xe_four (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (a : Fin 4) (i : Fin r) :
    T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i =
      ∑ k, (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k • T.xe y k := by
  fin_cases a
  · show T.xe (y + GlobalTheory.TensAct.latAct T A y) i = ∑ k, (1 + A) i k • T.xe y k
    rw [map_add (f := _), Pi.add_apply, GlobalTheory.TensAct.xe_latAct]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_one_smul]
  · show T.xe y i = ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    rw [sum_one_smul]
  · show T.xe (GlobalTheory.TensAct.latAct T A y) i = ∑ k, A i k • T.xe y k
    rw [GlobalTheory.TensAct.xe_latAct]
  · show T.xe 0 i = ∑ k, (0 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    simp only [map_zero, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

end Rows

end GlobalTheory.MumSide
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

abbrev Vec (r : ℕ) := Fin r ⊕ Fin r → ℤ

section Formal

variable {r : ℕ}

def lam (u v : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (u + v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 0 1

def theta (a b c : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (a + b + c) 1 - Finsupp.single (a + b) 1 - Finsupp.single (a + c) 1 - Finsupp.single (b + c) 1 +
    Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 - Finsupp.single 0 1

def xv (i : Fin r) : Vec r := Sum.elim (Pi.single i 1) 0

def zv (i : Fin r) : Vec r := Sum.elim 0 (Pi.single i 1)

def axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim (fun l => A i l) 0

def azv (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim 0 (fun l => A' i l)

def rosVec (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i : Fin r) : Vec r :=
  ![axv A i + zv i, axv A i, zv i, xv i + azv A' i, xv i, azv A' i] a

def sig (W A A' : Matrix (Fin r) (Fin r) ℤ) : Vec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • lam (rosVec A A' a i) (rosVec A A' a j)

end Formal

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def vecHom (T : Tens D D' W) (v : Vec r) : D'.P.A ⊗ D'.P.A ⟶ D.P.A :=
  (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k)

def vecLat (T : Tens D D' W) (v : Vec r) (y y' : D'.X) : D.X :=
  ∑ k, v (Sum.inl k) • T.xe y k + ∑ k, v (Sum.inr k) • T.xe y' k

def isoV {X X' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}
    (w : LB.Iso M' (LB.LinComb M ψ δ)) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι) (χ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ :=
  gm χ z _ (w.s (fun k => J (χ ≫ ψ k), J' χ))

def qv (T : Tens D D' W) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (χ : D'.X) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  ∏ i, ∏ j, val (D.tau (T.xe χ i) (T.xe χ j)) (𝟙 _) z J ^ W i j

def rosLat (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) : Fin 6 → D'.X :=
  ![GlobalTheory.TensAct.latAct T A y + y', GlobalTheory.TensAct.latAct T A y, y', y + GlobalTheory.TensAct.latAct T A' y', y,
    GlobalTheory.TensAct.latAct T A' y']

def Triv (T : Tens D D' W) (c : Vec r →₀ ℤ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb D.P.L (fun v : c.support => (vecHom T v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good D.P.L z J → ∀ y y' : D'.X,
      val Ξ (D'.pt2 y y') z J = ∏ v ∈ c.support, val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-(c v))

end GlobalTheory.TensBal
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

theorem stalkOf_closedPoint_isUnit {W : Type} [CommRing W] [IsLocalRing W] (v : W)
    (h : IsUnit (stalkOf (closedPoint W) v)) : IsUnit v := by
  have e : stalkOf (closedPoint W) = (stalkClosedPointIso (CommRingCat.of W)).inv.hom := by
    unfold stalkOf
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
    ext x
    simp
  rw [e] at h
  exact (isUnit_map_iff (stalkClosedPointIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv v).1 h

theorem isUnit_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α) (v : R), OrigVal D b v → eSec D.P.A (closedPoint R) ∈ nonzeroLocus b → IsUnit v := by
  intro R _ _ _ D k α b v hv hmem
  have hmem' : ∃ j, eSec D.P.A (closedPoint R) ∈ D.P.A.left.basicOpen (b.f j) := by
    unfold nonzeroLocus at hmem
    simpa [TopologicalSpace.Opens.mem_iSup] using hmem
  obtain ⟨j, hj⟩ := hmem'
  have hjU := D.P.A.left.basicOpen_le (b.f j) hj
  have hu := (Scheme.mem_basicOpen _ _ _ hjU).1 hj
  obtain ⟨J, hJ, -⟩ := exists_good (Z := Sp R) D.P.L D.P.isLB (closedPoint R) (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hsv := hv (closedPoint R) J hJ
  have e1 := sec_trans b (unitW D.P.A) (closedPoint R) (hJ.mem (D.famφB α) (unitW D.P.A)) hjU
  have hg : IsUnit (gs (unitW D.P.A) (closedPoint R) _ (b.f j)) := by
    rw [gs_eq _ _ _ hjU]
    have e2 := Scheme.Hom.germ_stalkMap_apply (eSec D.P.A) _ (closedPoint R) hjU (b.f j)
    exact e2 ▸ hu.map ((eSec D.P.A).stalkMap (closedPoint R)).hom
  have hs : IsUnit (sval b (unitW D.P.A) (closedPoint R) J) := by
    show IsUnit (gs _ _ _ _)
    rw [e1]
    exact (Units.isUnit _).mul hg
  rw [hsv] at hs
  exact stalkOf_closedPoint_isUnit v (isUnit_of_mul_isUnit_left hs)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m : ℕ) (H : Subgroup (𝟙_ (Over S) ⟶ A)), (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → (∀ h ∈ H, ∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) → (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 A) (lift 1 h₂) 1) → ∃ u : ∀ a : H × H, LB.Gen (LB.LinComb (GlobalTheory.UPel.HT.Hecke.lbPow P m) (K := Fin 2) ![𝟙 (G2 A).left, (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u (a * c)) (LB.mulGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ _ _ (u a) (LB.pullGen (GlobalTheory.UPel.HT.Hecke.lbPow P m) _ _ (u c) (GlobalTheory.UPel.HT.Hecke.transl (lift a.1.1 a.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left)) := by
  first | exact @GlobalTheory.IsoLin.exists_linearisation_isotropic | exact GlobalTheory.IsoLin.exists_linearisation_isotropic | (intros; apply GlobalTheory.IsoLin.exists_linearisation_isotropic <;> assumption)
end
