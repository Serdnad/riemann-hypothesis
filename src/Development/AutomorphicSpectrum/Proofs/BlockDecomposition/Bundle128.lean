module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle088
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle116
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Mathlib.Topology.Instances.Matrix
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrDelta
open GlobalTheory.CompanionTheory.CocProd

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem sqMap_val {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {T T' : C} (φ : T ⟶ T') (z : sqM a b T)
    (u : A.obj T) (h : z.1 = Ideal.Quotient.mk _ u) :
    (sqMap a b φ z).1 = Ideal.Quotient.mk _ ((A.map φ).hom u) := by
  obtain ⟨x, hx⟩ := z
  obtain rfl : x = _ := h
  rfl

variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T)

theorem Pmap_j_apply {T T' : C} (φ : T ⟶ T') (u : Φ.A.obj T) :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom ((Φ.A.map (Q.j T)).hom u) =
      (Φ.A.map (Q.j T')).hom ((Φ.A.map φ).hom u) := by
  exact (Cut.mapA_comp _ _ u).symm.trans
    ((congrArg (fun f => (Φ.A.map f).hom u) (Cut.Pmap_j Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).trans
      (Cut.mapA_comp _ _ u))

theorem Pmap_shift {T₀ T T' : C} (ψ : T₀ ⟶ T) (φ : T ⟶ T') :
    (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom
      (Q.X T + (Φ.A.map (Q.j T)).hom (E.a σ 0 ψ)) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 (ψ ≫ φ)) := by
  have h : (Φ.A.map (Cut.Pmap Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ)).hom (Q.X T) =
      Q.X T' + (Φ.A.map (Q.j T')).hom (E.a σ 0 φ) :=
    Cut.Pmap_X Q (X := (Pt.Sσ σ).obj T) (Y := (Pt.Sσ σ).obj T') φ
  rw [map_add (f := _), Pmap_j_apply, a_comp, map_add (f := _), h]
  abel

def Bv {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) : Φ.A.obj (Q.P (s.obj (Fin.last n))) :=
  Q.X _ + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.le_last p))))

theorem Bv_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Bv Q E σ s p ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
  have h : Bv Q E σ s p ∈ Φ.J.S _ := Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))
  rw [Nat.cast_one, hF.one]
  exact h

theorem term_val {Fil : ℤ → IdF Φ.A} {j : ℕ} {r : ℤ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j)
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (show sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1)))) from
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s))).1 =
      Ideal.Quotient.mk _ (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s)))) := by
  refine (sqMap_val (Fil r) (Fil (r + 1)) (Cut.Pmap Q (X := (Pt.Sσ σ).obj _) (Y := (Pt.Sσ σ).obj _) (toLast i s))
    (y (face i s)) _ (hy (face i s))).trans ?_
  have e : (face i s).map (homOfLE (Fin.zero_le (Fin.last j))) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove 0))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have h1 := Pmap_shift Q E σ ((face i s).map (homOfLE (Fin.zero_le (Fin.last j)))) (toLast i s)
  have h2 := Pmap_j_apply Q E σ (toLast i s) (E.form σ (Fin.succ ∘ I) x (face i s))
  rw [e] at h1
  exact congrArg (Ideal.Quotient.mk _) ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 h2))

theorem Bv_zero {n : ℕ} (s : ComposableArrows C (n + 1)) :
    Bv Q E σ s 0 = Bv Q E σ s 1 + (Φ.A.map (Q.j _)).hom (ga E σ 0 s 0 1 (Fin.zero_le _)) := by
  have e : s.map (homOfLE (Fin.le_last (0 : Fin (n + 2)))) =
      s.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ s.map (homOfLE (Fin.le_last (1 : Fin (n + 2)))) := by
    rw [← s.map_comp]; rfl
  unfold Bv ga
  rw [e, a_comp, map_add (f := _)]
  abel

theorem form_cons {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s =
      ga E σ 0 s 0 1 (Fin.zero_le _) * (Φ.A.map (toLast 0 s)).hom (E.form σ (Fin.succ ∘ I) x (face 0 s)) := by
  rw [face_form]
  have hl : (0 : Fin (j + 2)).succAbove (Fin.last j) = Fin.last (j + 1) := by simp
  have hW : (Φ.A.map (toLast 0 s)).hom ((Φ.A.map (σ _)).hom x) = (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x := by
    rw [map_map, show σ _ ≫ toLast 0 s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hl]
  rw [hW]
  unfold Frame.form
  rw [Fin.prod_univ_succ, mul_assoc]
  congr 2

theorem alt_sum {S S' F : Type*} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (J : F) (n : ℕ)
    (t : Fin (n + 1) → S) (b : Fin (n + 1) → S') (B : S') (g : S) (h0 : B = b 0 + J g)
    (hs : ∀ k : Fin n, b k.succ = B) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (b i * J (t i)) =
      B * J (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • t i) - J (g * t 0) := by

  rw [map_sum, Finset.mul_sum, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun i : Fin (n + 1) => B * J ((-1 : ℤ) ^ (i : ℕ) • t i))]
  have h : ∀ k : Fin n, (-1 : ℤ) ^ (k.succ : ℕ) • (b k.succ * J (t k.succ)) = B * J ((-1 : ℤ) ^ (k.succ : ℕ) • t k.succ) := by
    intro k
    rw [hs, map_zsmul, mul_smul_comm]
  rw [Finset.sum_congr rfl fun k _ => h k]
  simp only [Fin.val_zero, pow_zero, one_smul, map_mul, h0]
  ring

theorem gr_delta {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1))
    (hy : ∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s)))
    (hw : ∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  funext s
  apply Subtype.ext
  have hL : Subtype.val (CH.d _ j y s : sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Bv Q E σ s (i.succAbove 0) *
        (Φ.A.map (Q.j _)).hom ((Φ.A.map (toLast i s)).hom (E.form σ (Fin.succ ∘ I) x (face i s))))) := by
    change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r).map (toLast i s)).hom (y (face i s)) :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) = _

    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (term_val Q E σ I x y hy s i))
    rfl
  have hR : Subtype.val ((-(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w) s :
      sqM (Fil r) (Fil (r + 1)) (Q.P (s.obj (Fin.last (j + 1))))) =
      -Ideal.Quotient.mk _ ((Φ.A.map (Q.j _)).hom (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) :=
    congrArg Neg.neg (sqMap_val (Fil r) (Fil (r + 1)) (Q.j (s.obj (Fin.last (j + 1)))) (w s) _ (hw s))
  refine hL.trans (Eq.trans ?_ hR.symm)
  change Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _ =
    -Ideal.Quotient.mk ((Fil (r + 1)).S (Q.P (s.obj (Fin.last (j + 1))))) _
  rw [alt_sum (Φ.A.map (Q.j _)).hom (j + 1) _ (fun i => Bv Q E σ s (i.succAbove 0)) (Bv Q E σ s 0)
    (ga E σ 0 s 0 1 (Fin.zero_le _))
    (by simpa using Bv_zero Q E σ s) (fun k => by simp), ← map_neg, Ideal.Quotient.eq, form_cons]
  have hD := d_form_mem E σ hF hc j q (Fin.succ ∘ I) x hx s
  have hJ := (Fil (((j : ℤ) + q) + 1)).map_mem (Q.j (s.obj (Fin.last (j + 1)))) hD
  have e1 : (((j + q + 1 : ℕ) : ℤ)) = ((j : ℤ) + q) + 1 := by push_cast; ring
  rw [← e1] at hJ
  have hm := hF.mul 1 (j + q + 1) _ (Bv_mem Q E σ hF s 0) hJ
  have e2 : (((1 + (j + q + 1) : ℕ) : ℤ)) = r + 1 := by rw [hr]; push_cast; ring
  rw [e2] at hm
  convert hm using 1
  ring

end GlobalTheory.CompanionTheory.GrDelta
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

def Gp : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp {X Y Z} f g := m.G.map_comp (show X.T ⟶ Y.T from f) (show Y.T ⟶ Z.T from g)

def mPt (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pt.U E ⋙ sq a b) (Pt.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := (m.sqC c ha hb).τ X.T
  nat {X Y} φ x := (m.sqC c ha hb).nat (show X.T ⟶ Y.T from φ) x

end Pts

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T))

include he hρ in
theorem cut_mem {X Y : Cut E'} (φ : X ⟶ Y) :
    E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map φ.1) (e ≫ m.G.map Y.s) = 0 := by
  apply hρ Y.T
  have h := he 0 (X.s ≫ φ.1) Y.s
  rw [map_zero, Category.assoc, ← m.G.map_comp, h]
  exact φ.2

def G1 : Cut E' ⥤ Cut E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, cut_mem m E E' e he hρ φ⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp {X Y Z} f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 : SMor (Cut.Φ1 E) (Cut.Φ1 E') σ where
  G := G1 m E E' e he hρ
  ρ T := m.ρ T.T
  comm T r := m.comm T.T r
  nat {T T'} φ x := m.nat φ.1 x
  mem T x hx := m.mem T.T hx
  dp T k x hx := m.dp T.T k hx

def e1 : (Cut.E1 E).D ⟶ (G1 m E E' e he hρ).obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [Category.id_comp, m.G.map_id, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem fr1 : (m1 m E E' e he hρ).Fr (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaC (X : Pt E') : (Cut.P0 Q).obj ((Gp m E E' e).obj X) ⟶ (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q _ _ (m.G.map (Q'.j X.T))

theorem j_eta (X : Pt E') : Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gp m E E' e).obj X) ((G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem rho_eta (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T))) = Q'.X X.T := by
  have h1 : (Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X (m.G.map (Q'.j X.T)) _ (E.mem 0 _ _)
  rw [h1, Category.assoc, ← m.G.map_comp, he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X), Cut.sec_spec, if_pos rfl]

theorem eta_nat {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫ (etaC m E E' e he hρ Q Q' Y).1 =
      (etaC m E E' e he hρ Q Q' X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have e1 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ)
  have e2 : Q'.j X.T ≫ Cut.Pmap (X := X) (Y := Y) Q' φ = φ ≫ Q'.j Y.T := Cut.Pmap_j (X := X) (Y := Y) Q' φ
  have e3 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫
      (etaC m E E' e he hρ Q Q' Y).1 = Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 ≫
        m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
    rw [← Category.assoc, e1, Category.assoc, j_eta, ← Category.assoc (Q.j _), j_eta, ← m.G.map_comp, ← m.G.map_comp, e2]
  have e4 := Cut.truncation_hom_ext Q (X := (Gp m E E' e).obj X) (Y := (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj Y))
    (ψ := (Cut.P0 Q).map (show (Gp m E E' e).obj X ⟶ (Gp m E E' e).obj Y from m.G.map φ) ≫ etaC m E E' e he hρ Q Q' Y)
    (ψ' := etaC m E E' e he hρ Q Q' X ≫ (G1 m E E' e he hρ).map ((Cut.P0 Q').map (show X ⟶ Y from φ))) e3
  exact congrArg Subtype.val e4

def eta : Gp m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ G1 m E E' e he hρ where
  app X := etaC m E E' e he hρ Q Q' X
  naturality {X Y} φ := Cut.hom_ext (eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ)

def mP (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ sq a b) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := ((m.sqC c ha hb).τ (Q'.P X.T)).comp ((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
  nat {X Y} φ x := by
    have key : ∀ (φ : X.T ⟶ Y.T) (x : sqM a b (Q.P (m.G.obj X.T))),
        (m.sqC c ha hb).τ (Q'.P Y.T) (((sq a b).map (etaC m E E' e he hρ Q Q' Y).1).hom
          (((sq a b).map (Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ))).hom x)) =
        ((sq a' b').map (Cut.Pmap (X := X) (Y := Y) Q' φ)).hom
          ((m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom x)) := by
      intro φ x
      rw [← (m.sqC c ha hb).nat]
      congr 1
      have h := eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ
      have h2 := congrArg (fun t => ((sq a b).map t).hom x) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      exact h2
    exact key φ x

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickHom

theorem isNilpotent_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ} (h0 : p ≠ 0)
    (hp : IsNilpotent (p : B)) {x : B} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hp
  have key : ∀ M : ℕ, p ^ M ∣ (M * p).factorial := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (mul_dvd_mul ih (Nat.dvd_factorial (Nat.pos_of_ne_zero h0) le_rfl)).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  obtain ⟨c, hc⟩ := key N
  refine ⟨N * p, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hc]
  push_cast
  rw [hN]
  simp

variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}

theorem comp_eq (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (o : O) (x : b.R)
    (hx : Ideal.Quotient.mk b.I x = κ o) : g (s.a o) = Ideal.Quotient.mk T.J (T.i x) := by
  have h1 : F.Ov T.y.1.2 (g.comp s.a) := by
    have := F.ov_map (CommRingCat.ofHom g) s.ov
    rw [hg] at this
    exact this
  have h2 := F.ov_uniq h1 T.y.2
  have h3 := congrArg (fun f : O →+* _ => f o) h2
  have h4 : T.y.1.1 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk T.J (T.i x) := T.w x
  rw [← h4, hx]
  exact h3

variable (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

def homOf (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (f : 𝓛.D →+* T.B) (hf : f.comp 𝓛.i = T.i)
    (hfg : ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (f z) = g r) :
    liftObj s ht 𝓛 δ hδ hp hn ⟶ T :=
  have hdp : IsDPMorphism δ T.δ f :=
    (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers b.γ 𝓛.i δ hδ).2 T.δ f (by rw [hf]; exact T.compat)
  have hle : b.I.map 𝓛.i ≤ T.J.comap f := Ideal.map_le_iff_le_comap.1 hdp.1
  { φ := f
    u := fun j => j.elim
    comm := fun r => congrArg (fun e : b.R →+* T.B => e r) hf
    dp := hdp
    hle := hle
    pt := by
      have hq : (Ideal.quotientMap T.J f hle).comp 𝓛.j = g := by
        ext r
        obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
        rw [RingHom.comp_apply, ← hz]
        exact hfg r z hz
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have h1 : T.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
        refine Eq.trans ?_ h1.symm
        change Ideal.Quotient.mk T.J (f (𝓛.i r)) = _
        rw [← hf]
        rfl
      · refine Eq.trans ?_ hg
        rw [← hq]
        exact (congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
          (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J f hle)))) s.y₀).symm
    hx := fun j => j.elim
    hs := by
      have : IsEmpty (F.cr b ht κ).ι := inferInstanceAs (IsEmpty Empty)
      have h1 : (liftObj s ht 𝓛 δ hδ hp hn).s = 1 := rfl
      rw [s_eq_one ht T, h1, map_one, Finset.prod_of_isEmpty, one_mul]
    hv := fun j => j.elim }

theorem main (T : Thick (F.cr b ht κ)) :
    ∃ g : s.R →+* T.B ⧸ T.J,
      (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
        Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧
      F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧
      ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) →
        ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have hc : ∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
      Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r := by
    intro c r z hz
    have hpt : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle))
        (F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀) = T.y.1.2 := congrArg (fun y => y.1.2) c.pt
    have e := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle)))) s.y₀
    have hq : (Ideal.quotientMap T.J c.φ c.hle).comp 𝓛.j = g := hgu _ (e.trans hpt)
    have := congrArg (fun e : s.R →+* T.B ⧸ T.J => e r) hq
    refine Eq.trans ?_ this
    exact congrArg (Ideal.quotientMap T.J c.φ c.hle) hz
  refine ⟨g, hc, hg, fun u hu => ?_⟩
  have hJ : EtLift T.J := GlobalTheory.CompanionTheory.EtNil.etLift_of_nil T.J fun x hx =>
    isNilpotent_of_mem T.δ hp (T.adm.1 hp) hx
  obtain ⟨f, ⟨hf1, hf2, hf3⟩, hfu⟩ := GlobalTheory.CompanionTheory.EtaleLift.lift_hom_existsUnique s.a (fun k => (s.T k : s.R)) b.I κ 𝓛
    T.J hJ T.i g u (fun x hx => T.i_mem hx) (comp_eq s ht T hg) hu
  refine ⟨homOf s ht 𝓛 δ hδ hp hn T hg f hf1 hf3, hf2, fun c hck => ?_⟩
  have hcf : c.φ = f := hfu c.φ ⟨RingHom.ext c.comm, hck, hc c⟩
  exact Thick.Hom.ext hcf (funext fun j => j.elim)

end GlobalTheory.CompanionTheory.ThickHom
end

section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_mirProj (n : ℕ) : Continuous (mirabolicProjection k n) := by
  have hval : Continuous fun g : Mir k n =>
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp continuous_subtype_val
  have hblock : Continuous fun g : Mir k n =>
      ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
  have hinv : Continuous fun g : Mir k n => g⁻¹ := by
    exact continuous_inv
  refine Units.continuous_iff.2 ⟨hblock, ?_⟩
  have : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    funext g
    rw [map_inv]
  show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
  rw [this]
  exact hblock.comp hinv

end GlobalTheory.CompanionTheory.BZMirFun
end
end

section


theorem _root_.GlobalTheory.T.gallery_of_tubes_and_crossing : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.IdTube → PositivityTheory.RgEis.TubeChain → PositivityTheory.RgEis.Cross → PositivityTheory.RgEis.Gallery := by
  first | exact @GlobalTheory.CompanionTheory.RgEisGal.gallery | exact GlobalTheory.CompanionTheory.RgEisGal.gallery | (intros; apply GlobalTheory.CompanionTheory.RgEisGal.gallery <;> assumption)
end
