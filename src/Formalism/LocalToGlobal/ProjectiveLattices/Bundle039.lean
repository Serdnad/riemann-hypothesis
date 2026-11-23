module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Field

variable (c c' : Coeff l) (hle : c.F ≤ c'.F)

abbrev incF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def AlgOver (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_incF (τ : E →+* ℂ) (a : 𝓞 E) : incF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact h ((IntermediateField.inclusion c.le).toRingHom x)

variable {Xo : Moduli Dw l}

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have key : ∀ a : 𝓞 E, algebraMap c'.F S (embK c' τ a) = algebraMap c.F S (embK c τ a) := by
    intro a
    rw [← embK_incF hle τ a]
    exact h (embK c τ a)
  unfold IsEigAt
  simp only [key]

def FrPt.res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def FrPt.ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

theorem FrPt.res_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : (y.ext hle h).res hle h = y := rfl

variable {r : ℕ}

def unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (incF c c' hle))).Comp
    fin := (U (σ'.comp (incF c c' hle))).fin
    X := (U (σ'.comp (incF c c' hle))).X
    un := fun k x => FrPt.ext hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (incF c c' hle))).un k x) }

def IsBC {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (y.res hle h)

def CuspBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsBC hle f' as fs

def ActBC {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsBC hle f' as fs → IsBC hle (act' g f') as (fun i => act g (fs i))

end Field

section Comparison₂

variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} {r : ℕ}
  {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def OneMapTieC (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (cc : (unfBC hle U σ0').Comp → ℂ)
    (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspBC hle U ∧ ActBC hle act act' ∧
    OneMapRow Xo c' V (unfBC hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph

end Comparison₂

end Gen

section Dict

open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {n r : ℕ}

def MarkBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w

def CXiVal {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelW V hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (U₂ t) V hr (dict₂ t) ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy (U₂ t) V hr (dict₂ t) ι F ik φ h γ →
        rdU (U₂ t) (dδ t).cδ (dict₂ t h).1 (dict₂ t h).2 =
          c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F)

def actLev (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActLev (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

end Dict

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frMap (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

end Gen

section Rec

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (hL : LawsP T) (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

def SupRLeRec (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ) (i : ℕ)
    (η : (recB hL.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA (wEt D j i)) (wEt D j i).n η.1 ≤ (recB hL.toLawsCore).supN j _ sg η

end Rec

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
def toGoodR (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

theorem toGoodR_apply (c : Coeff l) (σ : c.F →+* ℂ) (x : c.F) : toGoodR c σ (σ x) = goodOf c σ x := by
  unfold toGoodR goodOf
  split_ifs <;> rfl

def toGood (c : Coeff l) (σ : c.F →+* ℂ) : CAt σ →ₐ[c.F] CAt (goodOf c σ) :=
  { (toGoodR c σ : ℂ →+* ℂ) with commutes' := fun x => toGoodR_apply c σ x }

theorem isIdOrConj_toGood (c : Coeff l) (σ : c.F →+* ℂ) : IsIdOrConj (toGood c σ) := by
  by_cases h : GoodEmb c σ
  · left; intro z
    show toGoodR c σ (toC z) = toC z
    unfold toGoodR; rw [if_pos h]; rfl
  · right; intro z
    show toGoodR c σ (toC z) = _
    unfold toGoodR; rw [if_neg h]

theorem rdEx_of (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : ∃ q, RdAt U σ y q := by
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨p, ψ, y0, hy0⟩ := hA (CAt σ) y
  have hg := goodEmb_goodOf c σ
  obtain ⟨z, hz⟩ := hB _ hg p y0 ((toGood c σ).comp ψ)
  have hm : FrMap (toGood c σ) y z := frMap_cancel _ _ _ ψ (toGood c σ) y0 y z hy0 hz
  obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 z
  exact ⟨⟨k, x, t⟩, z, toGood c σ, isIdOrConj_toGood c σ, hm, ht⟩


end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7}

variable (T : Top D)

namespace Top

abbrev PtA (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  PtV (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) (T.G.PY j (WeightAlgebra.resCh la)) (T.G.lies j la) la

def th (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) := thGen (T.Q.Xo j) T.Q.c (T.nab j) (wtA w) w.n

def sh (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) :=
  shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (wtA w) w.n (T.dδ j w.n)

end Top

variable {T} (h : LawsP T)

def recPJ (j : ℕ) (hj : InR D j) : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  mkX T.Q.eO T.C h.toLawsCore.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.toLawsCore.Nl h.toLawsCore.hNs
    h.toLawsCore.hNl h.toLawsCore.hle T.Cu T.Xc T.Xc_lat T.FJt h.toLawsCore.sg
    T.G.P j hj (h.toLawsCore.mul j hj) (T.G.dat j) (fun hm => (h.datum_condition j hj.1 hm).1) (fun hm => (h.datum_condition j hj.1 hm).2)
    (T.PtA j) (fun _ y => imgV y) (fun _ y => vAtV y) (fun _ y => isVal_vAt y)
    (fun _ f _ => nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) f) (T.th j) (T.sh j)

def recX : WeightAlgebra.Prov D (recB h.toLawsCore) T.G.P := fun j h1 h2 => recPJ h j ⟨h1, h2⟩

theorem recPJ_vAt_inc (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la)
    (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 := by
  dsimp only [recPJ, mkX, vG, incG]
  refine le_antisymm (iInf_le_of_le (deg w) (le_of_eq ?_)) (le_iInf fun m => ?_)
  · change vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff (deg w)) = _
    first
      | simp [AddMonoidAlgebra.coeff_single]
      | simp [AddMonoidAlgebra.single_apply]
      | simp [Finsupp.single_apply]
      | exact (0 : Nat)
  · change _ ≤ vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff m)
    by_cases hm : deg w = m
    · subst hm
      first
        | simp [AddMonoidAlgebra.coeff_single]
        | simp [AddMonoidAlgebra.single_apply]
        | simp [Finsupp.single_apply]
    · first
        | simp [AddMonoidAlgebra.coeff_single, hm]
        | simp [AddMonoidAlgebra.single_apply, hm]
        | simp [Finsupp.single_apply, hm]
      rw [(isVal_vAt y).zero]
      exact le_top

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem MuVal.eq_one_of_fixed {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}
    (h : MuVal V χ mu) (y : (AE D)ˣ)
    (hy : sigR (AF D.host.F) D.sp.cm.sig (y : AE D) = y) : χ y = 1 := by
  obtain ⟨x, hx⟩ := h.1 1
  have hxy : IsDetRoot V 1 (x * y) := by
    unfold IsDetRoot at hx ⊢
    rw [Units.val_mul, map_mul, hy, ← mul_assoc, ← hx]
  have e2 := h.2 1 (x * y) hxy
  rw [h.2 1 x hx, map_mul] at e2
  have e3 : χ x * 1 = χ x * χ y := by
    apply Subtype.ext
    simpa [Circle.coe_mul] using e2
  exact (mul_left_cancel e3).symm

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  (c : Coeff l)

private theorem rt0_conj_ne_lemma : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h2
  have hre := Complex.conj_eq_iff_re.mp h2
  have hsq := H.sqrt_neg_disc_sq
  rw [← hre] at hsq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h3 : ((H.rt0.re ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ) : ℝ) : ℂ) := by push_cast; exact hsq
  have h4 := Complex.ofReal_injective h3
  nlinarith [sq_nonneg H.rt0.re]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  unfold GoodEmb at h h'
  simp only [RingHom.comp_apply] at h h'
  rw [h] at h'
  exact rt0_conj_ne_lemma h'

private theorem imaginary_root_conj_lemma_2 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
  have h1 : ((starRingEnd ℂ) H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact absurd h rt0_conj_ne_lemma
  · exact h

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have key : ∀ τ : c.F →+* ℂ, GoodEmb c τ ∨ GoodEmb c ((starRingEnd ℂ).comp τ) := by
    intro τ
    unfold GoodEmb
    simp only [RingHom.comp_apply]
    generalize hxd : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = x
    have hx : (x : ℂ) = H.rt0 := by rw [← hxd]; rfl
    have hx2 : x ^ 2 = -((H.d : ℕ) : c.F) := by
      apply Subtype.ext
      have h0 : (x : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := by rw [hx, H.sqrt_neg_disc_sq]
      exact_mod_cast h0
    have hsq : (τ x) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hx2, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · right
      rw [h, map_neg, imaginary_root_conj_lemma_2, neg_neg]
  unfold goodOf
  by_cases h1 : GoodEmb c σ
  · have h2 := not_good_conj c h1
    rw [if_neg h2, if_pos h1]
    ext x
    simp
  · rcases key σ with h | h
    · exact absurd h h1
    · rw [if_pos h, if_neg h1]

end

variable {D : D7} {T : Core D} (h : LawsCore T)

theorem recB_supN_conj (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (F : (recB h).Cusp j w) :
    (recB h).supN j w ((starRingEnd ℂ).comp σ) F = (recB h).supN j w σ F := by
  simp [recB, mkB, cutN, Core.Ns, goodOf_conj]

end Formalism.L2.Pj
end
end
