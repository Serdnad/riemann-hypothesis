module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle044
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle005
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RestrictionEqZeroIffMemVanishingFiltration
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def nrmTieDefRd (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ) :=
  (rdEx_of U hU hA hB σ y).choose

end Gen

section Rec

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)


variable {j} in
def NrmTieKC (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) (F : (recB hL).Cusp j ka),
    nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P =
      recNrm (Tc.U j (goodOf Tc.Q.c (sgOf P))) (xiR D) (wtA ka) ka.n (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

def nrmTieDefPt (hj : InR D j) (hA : AllTest (Tc.Q.Xo j) Tc.Q.c)
    (hB : ∀ σ, GoodEmb Tc.Q.c σ → BCEx (Tc.Q.Xo j) Tc.Q.c σ) (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (hb : CBaseEx (Tc.Q.Xo j) Tc.Q.c h) (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ) :
    SupPtAt j (goodOf Tc.Q.c (sgOf P)) :=
  ⟨(nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).1,
    (nrmTieDefRd (Tc.U j) (hL.unf j hj) hA hB (sgOf P) (yPDef h hb Z P)).2.1⟩

end Rec

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D}



abbrev OmSK (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
    Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) (Jid (recPlus h j hj) la G.w)



def qZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F : (recB h.toLawsCore).Cusp j wF) : OmSK h j hj hG hT G la Z :=
  Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))
    (lwZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w
      (algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
        (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc wF F))))




def algZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Kp (recPlus h j hj) la G.N →+* OmSK h j hj hG hT G la Z :=
  (Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))).comp
    (algebraMap (Kp (recPlus h j hj) la G.N) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def TieSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  letI : ∀ Z, Module (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z) := fun Z =>
    (algZ h j hj hG hT G la Z).toModule
  (∃ e : SectionSheafQuotient (recPlus h j hj) la G.w wF ≃ₗ[Kp (recPlus h j hj) la G.N] (∀ Z, OmSK h j hj hG hT G la Z),
    ∀ (F : (recB h.toLawsCore).Cusp j wF) (Z : Comp (T.Q.Xo j) T.Q.c),
      e (resF G la F) Z * qZ h j hj hG hT G la Z g0 = qZ h j hj hG hT G la Z F) ∧
  G.del = ∑ᶠ Z : Comp (T.Q.Xo j) T.Q.c, Module.finrank (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z)





end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

def parAt : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datHolds D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datHolds D) j) l (datumAtLift_pq_pos D _ (datHolds D) j))
  eO := eOf D hF

def LevelPb (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
    l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PerFr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perFr_add {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v w : Fin r → E) (τ : E →+* ℂ)
    (i : ℕ) : perFr X x (v + w) τ i = perFr X x v τ i + perFr X x w τ i := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (v + w) = Data.emb σ v + Data.emb σ w := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_add _ _ _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [Matrix.mulVec_add]; done)
    | (simp [hermC, Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [Matrix.dotProduct_add, Matrix.mulVec_add, mul_add, add_mul, Finset.sum_add_distrib]; done)
    | (unfold hermC; simp [mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)])

theorem perFr_zero {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x 0 τ i = 0 := by
  have he : ∀ σ : E →+* ℂ, Data.emb σ (0 : Fin r → E) = 0 := by
    intro σ
    first
      | (funext k; simp [Data.emb]; done)
      | (simp [Data.emb]; done)
      | exact map_zero _
  unfold perFr
  simp only [he]
  split_ifs <;> first
    | (simp; done)
    | (simp [hermC]; done)
    | (unfold hermC; simp)

end PerFr

section Lin

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def eb {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : Fin g → ℂ :=
  Pi.single (e.symm ⟨τ, i⟩) 1

theorem eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (q : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eb e τ i (e.symm q) = if q = ⟨τ, i⟩ then 1 else 0 := by
  by_cases hq : q = ⟨τ, i⟩
  · subst hq
    simp [eb]
  · simp [eb, hq, Pi.single_apply, e.symm.injective.eq_iff]

theorem sum_eb_apply {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (τ : E →+* ℂ)
    (c : Fin (Dw.mult τ) → ℂ) (l : Fin (Dw.mult τ)) : (∑ j, c j • eb e τ j) (e.symm ⟨τ, l⟩) = c l := by
  simp [Finset.sum_apply, eb_apply]

end Lin

section Der

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} {e1 e2 : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e2 (h z) = e1 z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hv : IsDerivAt0 e1 w v) : IsDerivAt0 e2 (h w) v := by
  unfold IsDerivAt0 at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  have h0 : h 0 = 0 := map_zero h
  have h3 : e2 0 = e1 0 := by simpa [h0] using he 0
  refine ⟨h1.trans h3.symm, ?_⟩
  intro U hU f
  refine (h2 U hU f).trans ?_
  have hfun : (fun z => valAt' (e1 z) U f) =
      (fun y => valAt' (e2 y) U f) ∘ (LinearEquiv.toContinuousLinearEquiv h) := by
    funext z
    simp [he]
  rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
  simp [h0]

end Der

section Fam

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def pmOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) : (F.Di k).La →+ (Fin g → ℂ) where
  toFun a := fun j => perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  map_zero' := by
    funext j
    simp [perFr_zero]
  map_add' a b := by
    funext j
    simp [perFr_add]

def ExpUniq {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P P' : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P' →
    ∀ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) →
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b, gam a = a + l.M • b) →
      (∀ a, ∃ b, gam a = a + l.A • b) → (∀ a, P' (gam a) = h (P a)) →
      ∀ z, (F.ex i P' (h z)).left = (F.ex i P z).left

def ExpLin {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (m : ℕ) (w : Fin m → (Fin g → ℂ)) (vs : Fin m → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left))
      (cf : Fin m → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ j, IsDerivAt0 (fun z => (F.ex i P z).left) (w j) (vs j)) →
      IsDerivAt0 (fun z => (F.ex i P z).left) (∑ j, cf j • w j) v → IsCombAt (F.u i P) vs cf v

def ExpTan {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) : Prop :=
  ∀ i (P : (F.Di i).La →+ (Fin g → ℂ)), IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P →
    ∀ (w : Fin g → ℂ) (v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      IsDerivAt0 (fun z => (F.ex i P z).left) w v →
      IsTanAt (F.u i P) v ∧ ∀ j, w = Pi.single j 1 → IsEigAt c (e j).1 v

variable {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}

theorem derivAt_exists {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left, IsDerivAt0 (fun z => (F.ex i P z).left) w v := by
  obtain ⟨v, hv, -⟩ := (F.ex_diff i P hP).1 w
  exact ⟨_, hv⟩

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Main

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)

def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩

end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Genus

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

def PtOfSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  0 < wL.n → ∀ (L : Type) [Field L] [Algebra (Kp (recPlus h j hj) la G.N) L]
    (φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] L),
    ∃ (alg : T.Q.c.F →+* L) (y : letI := alg.toAlgebra; FrPt (T.Q.Xo j) T.Q.c L),
      (letI := alg.toAlgebra; ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (ψ : Om Z →ₐ[T.Q.c.F] L), FrMap ψ (genFr hG Z) y) ∧
      (∀ a : T.Q.c.F, alg a = algebraMap (Kp (recPlus h j hj) la G.N) L
        (@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)
          (algebraMap T.Q.c.F ((recPlus h j hj).Kl la) a))) ∧
      letI := alg.toAlgebra
      (∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
          (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
          evR (T.Q.Xo j) T.Q.c ((G.w k : T.R j)) y) ≠ 0 ∧
      ∀ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL k)),
        φ (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
          ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ g), emb_mem_Vw (recPlus h j hj) la G.N _ g⟩)) =
        evR (T.Q.Xo j) T.Q.c ((g : T.R j)) y /
          (∑ k', algebraMap (Kp (recPlus h j hj) la G.N) L
            (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k'))) *
            evR (T.Q.Xo j) T.Q.c ((G.w k' : T.R j)) y) ^ k

end Formalism.L2.Pj
end
end
