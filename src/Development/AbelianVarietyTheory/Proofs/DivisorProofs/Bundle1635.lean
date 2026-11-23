module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_of_mem (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dite_eq_left τ.2]

theorem perFr_of_conj (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dite_eq_left h2, dite_eq_left h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

theorem coord_eq_of_per_mem (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : X.p0 ≤ (a : ℕ)) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v τ.1 i) : (a : ℕ) = X.p0 + i := by
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = 1 := ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single a 1)
  rw [per_of_le X _ _ _ ha, perFr_of_mem, hm, inv_one, one_mulVec] at h1
  by_contra hne
  split_ifs at h1 with hi
  · have h2 : (⟨X.p0 + i, hi⟩ : Fin r) ≠ a := fun e => hne (by rw [← e])
    simp [Data.emb, Pi.single_eq_of_ne h2] at h1
  · simp [Data.emb] at h1

theorem coord_eq_of_per_conj (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : (a : ℕ) < X.p0) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v (conjEmb τ.1) i) : (a : ℕ) = X.p0 - 1 - i := by
  have hle := X.p0_le
  obtain ⟨s, t, hst⟩ : ∃ s t, X.Gm s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact X.Gm_det (Matrix.det_eq_zero_of_row_eq_zero a (hc a))
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = Matrix.single s a 1 :=
    ⟨fun _ => (Matrix.single s a 1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single t 1)
  rw [per_of_lt X _ _ _ ha, perFr_of_conj X _ _ τ i ⟨X.p0 - 1 - i, by omega⟩ rfl, hm] at h1
  by_contra hne
  have h2 : a ≠ (⟨X.p0 - 1 - i, by omega⟩ : Fin r) := fun e => hne (by rw [e])
  simp [hermC, FD.col, Data.emb, Matrix.single_apply, Pi.single_apply, h2, apply_ite, hst] at h1

theorem Dic.letter {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hσ : ∀ τ, Formalism.L2.PjFree.relab c σ τ = τ) (hm : ∀ τ, τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = perFr X x v τ i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, hσ, Equiv.apply_symm_apply] at this
  rw [hi, hσ, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    subst h1
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, rfl, by omega⟩
  · have h1 : τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    subst h1
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm _ ((X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, rfl, by omega⟩

end Letters


end GlobalTheory.AdTh
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

section Helpers
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ}

def twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (Fl (halfL g v)) (halfR g v)
  map_add' v w := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_add (f := _), Pi.add_apply]
  map_smul' c v := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem halfL_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfL g (twistLeft Fl v) = Fl (halfL g v) := halfL_append _ _

theorem halfR_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfR g (twistLeft Fl v) = halfR g v := halfR_append _ _

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem comp_psum {T T' : Over (Sp ℂ)} (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

end GlobalTheory.AdjPullFrame

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem ex_twistLeft {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistLeft Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A ≫ f, snd A A] I.down := by
  have e : (sqUnif A u).ex (twistLeft Fl v) = (sqUnif A u).ex v ≫ lift (fst A A ≫ f) (snd A A) := by
    change lift (u.ex (halfL g (twistLeft Fl v))) (u.ex (halfR g (twistLeft Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A ≫ f) (snd A A)
    rw [halfL_twistLeft, halfR_twistLeft, hFl, comp_lift, lift_fst_assoc, lift_snd]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

theorem ex_twistRight {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistMap Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A, snd A A ≫ f] I.down := by
  have e : (sqUnif A u).ex (twistMap Fl v) = (sqUnif A u).ex v ≫ lift (fst A A) (snd A A ≫ f) := by
    change lift (u.ex (halfL g (twistMap Fl v))) (u.ex (halfR g (twistMap Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A) (snd A A ≫ f)
    rw [halfL_twist, halfR_twist, hFl, comp_lift, lift_fst, lift_snd_assoc]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

end GlobalTheory.AdjPullFrame

end Helpers


open GlobalTheory.LamPullFrame GlobalTheory.ProdUnifSq GlobalTheory.AdjPullFrame in
theorem GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  intro A _ _ g hA _ N _ hN M u Hm χ hM hF f f' F F' _ _ hFe hF'e hadj
  have hp : IsProjOver A.hom := GlobalTheory.ProjSpace.isProjOver_of_relAmple hN
  obtain ⟨U1, h1ex, h1Λ, h1fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A ≫ f, snd A A] I.down)
    (fun I => sumL g I ∘ₗ twistLeft F) (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistLeft u f F hFe I v)
  obtain ⟨U2, h2ex, h2Λ, h2fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A, snd A A ≫ f'] I.down)
    (fun I => sumL g I ∘ₗ twistMap F') (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistRight u f' F' hF'e I v)
  let UN := GlobalTheory.SameFactor.divUnif U1 U2 (h2ex.trans h1ex.symm)
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
    (GlobalTheory.ProjSpace.isProjOver_pullback hp hp) _
    (LB.isLB_div (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)) (g + g) UN
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro w hw p z hz
  obtain ⟨hz2, hz1⟩ := (top_le_preimage_inf _ _ _).1 hz
  change ⊤ ≤ (U1.ex z).left ⁻¹ᵁ _ at hz1 hz2
  rw [h1ex] at hz1 hz2
  have hw' : w ∈ sqLat u.Λ := by
    have h : w ∈ U1.Λ := hw
    rw [h1Λ] at h
    exact h
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw'
  let j1 : (abelian₂ A M).ι := fun I => p.2 I
  let j2 : (abelian₂ A M).ι := fun I => p.1 I
  have hc1 : ⊤ ≤ ((sqUnif A u).ex (twistLeft F z)).left ⁻¹ᵁ (abelian₂ A M).U j1 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j1).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A ≫ f, snd A A] I.down).left) p.2).1 hz1 I
    rw [← Over.comp_left, ← ex_twistLeft u f F hFe I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hc2 : ⊤ ≤ ((sqUnif A u).ex (twistMap F' z)).left ⁻¹ᵁ (abelian₂ A M).U j2 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j2).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ f'] I.down).left) p.1).1 hz2 I
    rw [← Over.comp_left, ← ex_twistRight u f' F' hF'e I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hwt1 : twistLeft F w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨?_, by rw [halfR_twistLeft]; exact hr⟩
    rw [halfL_twistLeft, ← u.ker, hFe, (u.ker _).2 hl, MonObj.one_comp]
  have hwt2 : twistMap F' w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨by rw [halfL_twist]; exact hl, ?_⟩
    rw [halfR_twist, ← u.ker, hF'e, (u.ker _).2 hr, MonObj.one_comp]
  have fac1 := lam_factor hM u u rfl hF j1 (twistLeft F z) (twistLeft F w) hwt1 hc1
  have fac2 := lam_factor hM u u rfl hF j2 (twistMap F' z) (twistMap F' w) hwt2 hc2
  rw [halfL_twistLeft, halfL_twistLeft, halfR_twistLeft, halfR_twistLeft, ← map_add (f := _)] at fac1
  rw [halfL_twist, halfL_twist, halfR_twist, halfR_twist, ← map_add (f := _)] at fac2
  have sw := GlobalTheory.AnyAppellHumbert.hermForm_swap hF.1
  have hE : hf Hm (F (halfL g z)) (halfR g w) + hf Hm (halfR g z) (F (halfL g w)) + hf Hm (F (halfL g w)) (halfR g w) =
      hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) + hf Hm (halfL g w) (F' (halfR g w)) := by
    have e1 : hf Hm (F (halfL g z)) (halfR g w) = hf Hm (halfL g z) (F' (halfR g w)) := hadj _ _
    have e3 : hf Hm (F (halfL g w)) (halfR g w) = hf Hm (halfL g w) (F' (halfR g w)) := hadj _ _
    have e2 : hf Hm (halfR g z) (F (halfL g w)) = hf Hm (F' (halfR g z)) (halfL g w) := by
      change hermForm Hm (halfR g z) (F (halfL g w)) = hermForm Hm (F' (halfR g z)) (halfL g w)
      rw [sw (F (halfL g w)) (halfR g z), hadj, ← sw]
    rw [e1, e2, e3]
  rw [hE] at fac1
  have n1 : (lamUnif u u rfl).fr j1 (twistLeft F (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add (f := _), ex_add_mem (sqUnif A u) _ hwt1]
    exact hc1
  have n2 : (lamUnif u u rfl).fr j2 (twistMap F' (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add (f := _), ex_add_mem (sqUnif A u) _ hwt2]
    exact hc2
  have hP1 : ∀ v, U1.fr p.2 v = (lamUnif u u rfl).fr j1 (twistLeft F v) := fun v => by
    refine (h1fr p.2 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j1 (twistLeft F v)).symm)
    rfl
  have hP2 : ∀ v, U2.fr p.1 v = (lamUnif u u rfl).fr j2 (twistMap F' v) := fun v => by
    refine (h2fr p.1 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j2 (twistMap F' v)).symm)
    rfl
  have hUN : ∀ v, UN.fr p v = U2.fr p.1 v * (U1.fr p.2 v)⁻¹ := fun v => rfl
  rw [hUN, hUN, hP1, hP1, hP2, hP2, fac1, fac2]
  have ne := Complex.exp_ne_zero (↑Real.pi * (hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) +
    hf Hm (halfL g w) (F' (halfR g w))))
  field_simp
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (κ : Type) [Fintype κ] (Λ : Submodule (Fv F v) ((κ → Fv F v) × (κ → Fv F v))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank (Fv F v) Λ = Fintype.card κ →
    ∀ l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₁ (schr ψv w φ) = l₁ φ) →
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₂ (schr ψv w φ) = l₂ φ) →
    (∃ φ ∈ SB (κ → Fv F v), l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.LagrInvForm.proportional_at_place | exact GlobalTheory.LagrInvForm.proportional_at_place | (intros; apply GlobalTheory.LagrInvForm.proportional_at_place <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

def theory (p : ℕ) [Fact p.Prime] : Theory p :=
  let Bc := (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose
  let Be := (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose
  let hB := GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale p Bc Be (GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms p).choose_spec (GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality p Bc).choose_spec
  let hV := GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase p hB.choose
  { base := hB.choose, katz := hB.choose_spec.1, etDual := hB.choose_spec.2, V := hV.choose,
    F_V := hV.choose_spec.1, V_F := hV.choose_spec.2 }

end GlobalTheory.Dieu
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

open GlobalTheory.BCT

theorem mem_map_conj_iff_term {G : Type} [Group G] (K : Subgroup G) (y z : G) :
    z ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cptPart_le_self_term {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T :=
  Subgroup.closure_le _ |>.mpr fun _ ht => ht.1

theorem inf_relIndex_of_le_left_term {G : Type} [Group G] {A B C : Subgroup G} (h : C ≤ A) :
    (A ⊓ B).relIndex C = B.relIndex C := by
  unfold Subgroup.relIndex
  congr 1
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_right (h hc)

theorem avg_eq_one_of_forall_term {H : Type} [Group H] (u : H → ℂ) (hu : ∀ k, u k = 1) : avg u = 1 := by
  have hs : rStab u = ⊤ := by
    ext k; simp only [Subgroup.mem_top, iff_true]; intro x; rw [hu, hu]
  have hi : (rStab u).index = 1 := Subgroup.index_eq_one.2 hs
  have hsub : Subsingleton (H ⧸ rStab u) := by
    have hc : Nat.card (H ⧸ rStab u) = 1 := hi
    exact (Nat.card_eq_one_iff_unique.1 hc).1
  unfold avg
  rw [hi, finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ rStab u) (fun q hq => absurd (Subsingleton.elim q _) hq), hu]
  simp

theorem twTerm_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hK δ f fv hf hcomm hstab hwt hev x
  have hT : ∀ y, y ∈ twCent θ δ ↔ ∀ v, pf v y ∈ twCent (θv v) (pf v δ) := fun y => GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ y
  have hC : ∀ y, y ∈ cptPart (twCent θ δ) ↔ ∀ v, pf v y ∈ cptPart (twCent (θv v) (pf v δ)) :=
    GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) hT hcomm
  have hgood := hev.and (hX.eventually_mem x)
  have hCg : cptPart (twCent θ δ) = ⨅ v, (cptPart (twCent (θv v) (pf v δ))).comap (pf v) := by
    ext y; rw [hC, Subgroup.mem_iInf]; rfl
  have hHg : (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom =
      ⨅ v, ((K v).map (MulAut.conj (pf v x)).toMonoidHom).comap (pf v) := by
    ext y
    simp only [mem_map_conj_iff_term, Subgroup.mem_iInf, Subgroup.mem_comap, map_mul, map_inv]
  have hloc : ∀ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) = ((K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := fun v => inf_relIndex_of_le_left_term (cptPart_le_self_term _)
  have hCH : ∀ᶠ v in cofinite, cptPart (twCent (θv v) (pf v δ)) ≤ (K v).map (MulAut.conj (pf v x)).toMonoidHom :=
    hgood.mono fun v hv c hc => by
      rw [mem_map_conj_iff_term]
      exact mul_mem (mul_mem (inv_mem hv.2) (hv.1.2.2 hc)) hv.2
  have hrel : (twCent θ δ ⊓ (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent θ δ)) = ∏ᶠ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := by
    rw [inf_relIndex_of_le_left_term (cptPart_le_self_term _), hHg, hCg]
    simp only [hloc]
    exact GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod pf K hX (fun v => cptPart (twCent (θv v) (pf v δ)))
      (fun v => (K v).map (MulAut.conj (pf v x)).toMonoidHom)
      (fun v => by rw [← hloc]; exact (hwt v (pf v x)).2) hCH
  let u : ∀ v, K v → ℂ := fun v k => fv v ((pf v x * k)⁻¹ * pf v δ * θv v (pf v x * k))
  have hfun : (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩ := by
    funext k; rw [hf]; congr 1; funext v; simp only [u, map_mul, map_inv, hθ]
  have hu1 : ∀ᶠ v in cofinite, ∀ k, u v k = 1 := hgood.mono fun v hv k => by
    have hk : pf v x * (k : Y v) ∈ K v := mul_mem hv.2 k.2
    simp only [u]
    rw [hv.1.1, Set.indicator_of_mem (show _ ∈ (K v : Set (Y v)) from
      mul_mem (mul_mem (inv_mem hk) hv.1.2.1) (hK v _ hk))]
    rfl
  have havg : avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      ∏ᶠ v, avg (u v) := by
    rw [hfun]; exact GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod pf K hX u (fun v => hstab v (pf v x)) hu1
  have hfa : Function.HasFiniteMulSupport fun v => (((twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) : ℕ) : ℂ) :=
    (eventually_cofinite.1 hCH).subset fun v hv h => hv (by
      show ((_ : ℕ) : ℂ) = 1
      rw [hloc, Subgroup.relIndex_eq_one.2 h, Nat.cast_one])
  have hfb : Function.HasFiniteMulSupport fun v => avg (u v) :=
    (eventually_cofinite.1 hu1).subset fun v hv h => hv (avg_eq_one_of_forall_term _ h)
  unfold twTerm
  rw [hrel, havg, Nat.cast_finprod', ← finprod_mul_distrib hfa hfb]

end GlobalTheory.EulerAbs
end
