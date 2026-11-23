module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechPts

open CategoryTheory.Limits

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

def baseOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) : U ⟶ X :=
  (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)).app (op U) z

def compOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) : U ⟶ Y :=
  (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i).app (op U) z

theorem compOf_comp {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f z i ≫ f = baseOf f z := by
  have e := WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i
  have := congrArg (fun t => t.app (op U) z) e
  exact this

theorem ext_comp {k : ℕ} {U : Scheme.{0}} (z z' : Sx (cech f) k U)
    (hb : baseOf f z = baseOf f z') (hc : ∀ i, compOf f z i = compOf f z' i) : z = z' := by
  apply yonedaEquiv.symm.injective
  apply WidePullback.hom_ext (fun _ : Fin (k + 1) => yoneda.map f)
  · intro i
    have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hc i
    exact yonedaEquiv.injective this
  · have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hb
    exact yonedaEquiv.injective this

theorem baseOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    baseOf f (cechPt f k x y h) = x := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp x)

theorem compOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x)
    (i : Fin (k + 1)) : compOf f (cechPt f k x y h) i = y i := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) i
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp (y i))

theorem baseOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) :
    baseOf f (Sx.res g z) = g ≫ baseOf f z :=
  NatTrans.naturality_apply (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) g.op z

theorem compOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f (Sx.res g z) i = g ≫ compOf f z i :=
  NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) g.op z

theorem baseOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) :
    baseOf f (Sx.along z θ) = baseOf f z := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp)
  exact congrArg (fun t => t.app (op U) z) e

theorem compOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    compOf f (Sx.along z θ) i = compOf f z (θ.toOrderHom i) := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp) i
  exact congrArg (fun t => t.app (op U) z) e

theorem map_aug {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    Sx.map (_root_.GlobalTheory.EtC.cechAug f) z = baseOf f z := rfl

theorem cechPt_spec : CrystallineSemistableComparison.E.CechPt := by
  intro Y X f k U
  refine ⟨fun z => ⟨baseOf f z, compOf f z, compOf_comp f z, ?_⟩, ?_, ?_⟩
  · exact ext_comp f _ _ (baseOf_cechPt f _ _ _).symm fun i => (compOf_cechPt f _ _ _ i).symm
  · intro x y h x' y' h' e
    funext i
    rw [← compOf_cechPt f x y h i, e, compOf_cechPt]
  · intro x y h
    refine ⟨?_, ?_, ?_⟩
    · rw [map_aug, baseOf_cechPt]
    · intro V g
      apply ext_comp
      · rw [baseOf_res, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_res, compOf_cechPt, compOf_cechPt]
    · intro p θ
      apply ext_comp
      · rw [baseOf_along, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_along, compOf_cechPt, compOf_cechPt]

end GlobalTheory.CompanionTheory.CechPts
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeProduct

variable {q : ℕ} {C : Type 1} [Category.{0} C]

def secPair (P : Probe C q) (i i' : ℤ) (s t r : ℕ) (h : s + t = r) :
    Pairing ((P.res i).K s) ((P.res i').K t) ((P.res (i + i')).K r) where
  μ c := LinearMap.mk₂ ℤ
    (fun (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (s : ℤ)) (P.U c)) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (t : ℤ)) (P.U c)) =>
      (twPair q i i').mul (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) a b)
    (fun a a' b => by simp)
    (fun n a b => by simp)
    (fun a b b' => by simp)
    (fun n a b => by simp)
  nat {c c'} φ x y := ((twPair q i i').nat (P.S.map φ).unop (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y).symm

def resPair [NeZero q] (hK : KapMul) (hT : InTw) (P : Probe C q) (i i' : ℤ) :
    ResPair (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q)) where
  μ := secPair P i i'
  ι c x y := hK hT q i i' (P.U c) (P.ζ c) x y
  leib s t r h c x y := by
    have e := (twPair q i i').leibniz (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y
    have e2 : ((s : ℤ).negOnePow : ℤˣ) • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) =
        (-1 : ℤ) ^ s • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) := by
      rw [Units.smul_def, Int.coe_negOnePow_natCast]
    rw [e2] at e
    exact e

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem term_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i : ℤ) (j : ℕ)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin 1 → Fin (n + 1)) (hg : Monotone g) :
    term ((P.res i).K j) s (Y.glob i j a) g hg = Sec.res (Y.y (s.obj (Fin.last n))) a := by
  simp only [CH.term, Probe.Pts.glob, Probe.res, secF]
  show Sec.res _ (Sec.res _ a) = _
  rw [res_res]
  congr 1
  exact Y.nat _

theorem cupC_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i i' : ℤ) (j j' n : ℕ) (h : j + j' = n)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (j' : ℤ)) X) :
    (secPair P i i' j j' n h).cupC (add_zero 0) (Y.glob i j a) (Y.glob i' j' b) =
      Y.glob (i + i') n ((twPair q i i').mul X (j : ℤ) (j' : ℤ) (n : ℤ) (by omega) a b) := by
  simp only [CH.Pairing.cupC, secPair]
  funext s
  simp only [LinearMap.mk₂_apply, term_glob]
  rw [← (twPair q i i').nat]
  rfl

theorem cast_cup {E : Spc} {n m k i j : ℤ} (h : n + m = k) (hc : n + m = k) (x : Ht q E n i) (y : Ht q E m j) :
    Ht.cast hc rfl (GlobalTheory.EtC.cup q x y) = (twPair q i j).cup E h x y := by
  subst hc
  rfl

theorem etCup : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.EdgeCup → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepCup →
    CrystallineSemistableComparison.E.KapMul → CrystallineSemistableComparison.E.EtCup := by
  intro hSpec hGood hEdge hBasic hRC hK hG hT q _ C _ P X Y i i' i'' hi j j' j'' hj x y
  subst hi
  have h : (j : ℤ) + (j' : ℤ) = (j'' : ℤ) := by omega
  rw [cast_cup h]
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i)) X (j : ℤ)).1 x
  obtain ⟨b, hb⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i')) X (j' : ℤ)).1 y
  have hab := hRC (ZMod q) _ _ _ (twPair q i i') X _ _ _ h x y a b ha hb
  have ea := (hSpec hG q C P X Y i j x).1 a ha
  have eb := (hSpec hG q C P X Y i' j' y).1 b hb
  have e := hEdge ℤ C P.L P.L P.L (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q))
    (resPair hK hT P i i') (hGood hG q C P i) (hGood hG q C P i') j j' j'' hj
    (Y.glob i j a) (Y.glob i' j' b) (Y.et i j x) (Y.et i' j' y) ea eb
  have e' := (congrArg (fun z => (P.res (i + i')).Edge z
    ((mulP (lcF P.S q)).cup hj (Y.et i j x) (Y.et i' j' y))) (cupC_glob P Y i i' j j' j'' hj a b)).mp e
  exact ((hSpec hG q C P X Y (i + i') j'' _).2 _ ⟨_, hab, e'⟩).symm

end GlobalTheory.CompanionTheory.EdgeProduct
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairCupFirst

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R}
  {T₁ : Res.{1} F₁} {T₂ : Res.{1} F₂} {T₃ : Res.{1} F₃} {P : Pairing F₁ F₂ F₃}

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} {T : Res.{1} F} (hT : T.Good) {s p n : ℕ}
    (σ : ComposableArrows C n) (a : Cn (T.K s) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (s + 1)) σ (T.dvC s p a) g hg = T.dv s _ (term (T.K s) σ a g hg) := by
  delta CrystallineSemistableComparison.CH.term CrystallineSemistableComparison.E.Res.dvC
  exact (hT.dv_nat s _ _).symm

theorem dvC_cupC (μ : ResPair T₁ T₂ T₃ P) (h₁ : T₁.Good) (h₂ : T₂.Good) {s t r k : ℕ} (h : s + t = r)
    (a : Cn (T₁.K s) k) (y : Cn (T₂.K t) 0) (hy : T₂.dvC t 0 y = 0) :
    T₃.dvC r k ((μ.μ s t r h).cupC (add_zero k) a y) =
      (μ.μ (s + 1) t (r + 1) (by omega)).cupC (add_zero k) (T₁.dvC s k a) y := by
  delta CrystallineSemistableComparison.E.Res.dvC CrystallineSemistableComparison.CH.Pairing.cupC
  funext σ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk₂_apply]
  have hz : ∀ (g : Fin (0 + 1) → Fin (k + 1)) (hg : Monotone g),
      CrystallineSemistableComparison.CH.term (T₂.K (t + 1)) σ (0 : Cn (T₂.K (t + 1)) 0) g hg = 0 := fun g hg => by
    delta CrystallineSemistableComparison.CH.term
    exact map_zero _
  rw [μ.leib, ← term_dvC h₂ σ y, hy, hz, map_zero, smul_zero, add_zero, ← term_dvC h₁ σ a]
  rfl

theorem stCupA : CrystallineSemistableComparison.E.CupLeib.{1} → CrystallineSemistableComparison.E.StCupA := by
  intro hL R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ h₁ h₂ i t n z y u hy hdy hst s
  induction s with
  | zero =>
    intro k r h x hx
    obtain ⟨hik, rfl⟩ := hx
    subst hik
    obtain rfl : r = t := by omega
    exact hst
  | succ s ih =>
    intro k r h x hx
    obtain ⟨a, rfl, hsa⟩ := hx
    obtain rfl : r = s + t + 1 := by omega
    show ∃ a', T₃.dvC (s + t) k a' = _ ∧
      T₃.St u (s + t) (k + 1) ((-1) ^ k • CrystallineSemistableComparison.CH.d (T₃.K (s + t)) k a')
    refine ⟨(μ.μ s t (s + t) rfl).cupC (add_zero k) a y, dvC_cupC μ h₁ h₂ rfl a y hy, ?_⟩
    have hcup := hL R C (T₁.K s) (T₂.K t) (T₃.K (s + t)) (μ.μ s t (s + t) rfl) k 0 k (add_zero k) a y
    rw [hcup, hdy, map_zero, smul_zero, add_zero, ← LinearMap.smul_apply, ← map_zsmul]
    exact ih (k + 1) (s + t) rfl _ hsa

end GlobalTheory.CompanionTheory.StairCupFirst
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem edgeCup_of_steps : CrystallineSemistableComparison.E.CupCls → CrystallineSemistableComparison.E.StTop → CrystallineSemistableComparison.E.StCupA → CrystallineSemistableComparison.E.StCupB → CrystallineSemistableComparison.E.EdgeCup := by
  intro hCls hTop hA hB
  unfold CrystallineSemistableComparison.E.EdgeCup
  intro R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn x y a b hx hy
  obtain ⟨z, hz, hzx, rfl⟩ := hx
  obtain ⟨z', hz', hzy, rfl⟩ := hy
  obtain ⟨hu, hcls⟩ := hCls R C F₁ F₂ F₃ P i j n hn z z' hz hz'
  refine ⟨P.cupC hn z z', hu, ?_, hcls.symm⟩
  have hyy := hTop R C F₂ T₂ hT₂ j z' hz' j 0 y hzy
  have hb := hB R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n hn z z' hz j 0 i (add_zero i) y hzy
  exact hA R C F₁ F₂ F₃ T₁ T₂ T₃ P μ hT₁ hT₂ i j n z y (P.cupC hn z z') hyy.1 hyy.2 hb i 0 n hn x hzx

end GlobalTheory.CompanionTheory.EdgeMap
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeClass

theorem edgeUniq_of : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StAdd → CrystallineSemistableComparison.E.StUniq → CrystallineSemistableComparison.E.EdgeUniq := by
  intro _ hadd huniq R _ C _ F T hG j x x' h h' hx hx'
  obtain ⟨z, hz, st, rfl⟩ := hx
  obtain ⟨z', hz', st', rfl⟩ := hx'
  refine ⟨⟨z + z', ?_, (hadd R C F T j z z' j 0 x x' st st').1, ?_⟩, ?_⟩
  · rw [map_add (f := _), hz, hz', add_zero]
  · rfl
  · intro hv
    have st2 : T.St (z - z') j 0 (x - x') := (hadd R C F T j z z' j 0 x x' st st').2
    have hB : z - z' ∈ (cx F).B j := by
      cases j with
      | zero => exact huniq R C F T hG 0 (z - z') 0 0 (x - x') st2 hv
      | succ s =>
        obtain ⟨b, hb, hbx⟩ := hv
        obtain ⟨a, hax, sta⟩ := st2
        refine huniq R C F T hG (s + 1) (z - z') s 1 _ sta ?_
        refine ⟨a - b, ?_, ?_⟩
        · rw [map_sub, hax, hbx, sub_self]
        · rw [map_sub, hb, sub_zero, pow_zero, one_smul]
    exact (Submodule.Quotient.eq _).2 hB

end GlobalTheory.CompanionTheory.EdgeClass
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

theorem locSplit : CrystallineSemistableComparison.E.LocSplit := by
  intro U hU P hP
  obtain ⟨S, hS, hSP⟩ := hP
  rw [Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have hsurj : Surjective (Limits.Sigma.desc 𝒰.f) := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]
  have het : Etale (Limits.Sigma.desc 𝒰.f) := by
    have := 𝒰.sigma.map_prop ⟨⟩
    simpa [Scheme.Cover.sigma_f] using this
  obtain ⟨s, hs⟩ := hU _ (Limits.Sigma.desc 𝒰.f) het hsurj
  have hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1) := by
    intro t
    have hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i)) := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i ∈ t
      · convert isOpen_univ
        ext
        simp [hi]
      · convert isOpen_empty
        ext
        simp [hi]
    exact hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)
  refine ⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩
  intro V g a hg
  have hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a) := by
    rintro _ ⟨v, rfl⟩
    have h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a := hg v
    rcases hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩
    rw [hq] at h1
    subst h1
    refine ⟨y, ?_⟩
    have h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v) := by rw [← hq]; simp
    rw [sigmaMk_mk] at h2
    rw [h2, Scheme.Hom.comp_apply]
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s :=
    ⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩
  have hgl : g = l ≫ 𝒰.f a := by
    have h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f := by simp
    rw [h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]
  rw [hgl]
  exact hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)

end GlobalTheory.CompanionTheory.LocSplitProof
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem repConc_of_inputs : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc := by
  intro hEv hSch hRep R _ I X n a
  have hS := hSch R X I (n - 1) n (n + 1) (by ring) rfl
  have hR := hRep R I X n
  have hconc : Sec.map (I.d n (n + 1)) a = 0 →
      ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a := by
    intro ha
    obtain ⟨α, h0, h1⟩ := hS.1 a ha
    refine ⟨α, ?_⟩
    unfold CrystallineSemistableComparison.E.IsConc
    exact ⟨h0, h1⟩
  have huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y := by
    intro x y hx hy
    have hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a) := (hR.2.2.1 x y a a hx hy).2
    rw [sub_self] at hxy
    obtain ⟨γ, hγ, hγa⟩ := hxy
    have h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0 := by
      have h := (hR.2.2.1 x x a a hx hx).2
      rwa [sub_self, sub_self] at h
    obtain ⟨b, hb⟩ := hR.2.2.2.1 0 h00 (n - 1) (by ring)
    have hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0 := ((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩
    rw [← sub_eq_zero, ← hγ, hγ0]
  refine ⟨hconc, fun x hx => ?_, huniq⟩
  have hx' := hx
  obtain ⟨β, hβ, hβa⟩ := hx'
  have ha : Sec.map (I.d n (n + 1)) a = 0 := by
    have h := (hS.2 β).1
    rwa [hβa] at h
  obtain ⟨α, hα⟩ := hconc ha
  have hα' := hα
  unfold CrystallineSemistableComparison.E.IsConc at hα'
  obtain ⟨hα1, -⟩ := hα'
  have hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a := by
    unfold CrystallineSemistableComparison.E.Rep
    refine ⟨α, rfl, ?_⟩
    rw [hα1 X (𝟙 X)]
    simp [GlobalTheory.EtC.Sec.res]
  exact ⟨α, hα, huniq _ _ hRα hx⟩

end GlobalTheory.CompanionTheory.EdgeMap
end
