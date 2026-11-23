module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.LocalToGlobal.NumberFieldFamilies.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Mem.Col2.HAt.Stab

theorem co_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    co S h (g x) = (reGL h E (Formalism.L2.Herm.toGLb S.frame g)).1 *ᵥ co S h x := by
  have e : lin S h (reGL h E (Formalism.L2.Herm.toGLb S.frame g)) = g := by
    subst h
    have e0 : ∀ k : GL (Fin S.rank) E, reGL rfl E k = k := fun k => by
      ext a b
      simp [reGL]
    show (Formalism.L2.Herm.toGLb S.frame).symm (reGL rfl E (reGL rfl E (Formalism.L2.Herm.toGLb S.frame g))) = g
    rw [e0, e0, MulEquiv.symm_apply_apply]
  rw [← co_lin, e]

theorem co_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (k : GL (Fin S.rank) E) (x : S.V) :
    co S h ((Formalism.L2.Herm.toGLb S.frame).symm k x) = (reGL h E k).1 *ᵥ co S h x := by
  rw [co_apply, MulEquiv.apply_symm_apply]

theorem eq_of_frMul {E K ι : Type} [Field E] [Field K] [Fintype ι] (τ : ι) (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ}
    (g M : GL (Fin n) E) (y : Col2.Fr emb σ n) (h : frMul emb σ M⁻¹ (frMul emb σ g y) = y) : g = M := by
  have h1 : (M⁻¹ : GL (Fin n) E).1.map (embAt σ emb τ) * (g.1.map (embAt σ emb τ) * y.1 τ) = y.1 τ :=
    congrFun (congrArg Subtype.val h) τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul] at h1
  have hy : IsUnit (y.1 τ) := (Matrix.isUnit_iff_isUnit_det _).2 (y.2 τ)
  have h2 : (M⁻¹ * g : GL (Fin n) E).1.map (embAt σ emb τ) = 1 := hy.mul_right_cancel (by rw [h1, Matrix.one_mul])
  have h3 : (M⁻¹ * g : GL (Fin n) E).1 = 1 := by
    apply Matrix.map_injective (embAt σ emb τ).injective
    show _ = (1 : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  have h4 : M⁻¹ * g = 1 := Units.ext h3
  exact (inv_mul_eq_one.1 h4).symm

theorem ext_vec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {x y : Fin N → E} (h1 : iniH hN x = iniH hN y)
    (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext j
  by_cases hj : j.1 < n
  · exact congrFun h1 ⟨j.1, hj⟩
  · have : j = Br.iL hN := Fin.ext (by have := j.2; show j.1 = n; omega)
    rw [this, h2]

theorem ga_eq_gam_mv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP), ((F u).til.ga c).1.1 = ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 := by
  intro B X I l Z H F hF u c
  classical
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  let y : Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) := ⟨fun _ => 1, fun _ => by simp⟩
  let g : GL (Fin (B.R.N B.R.m)) B.fields.E := ((F u).til.ga c).1
  let φ : (I.stp u I.mu0 B.R.m).Cl → Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ := fun _ z => if z = y then 1 else 0
  have hY := (hF u).eY B.R.m le_rfl (Or.inr rfl)
  have h := (F u).evz φ c (frMul B.fields.emb B.embLL g y) y (by
    intro τ
    rw [hemb]
    exact (congrFun (hY _) τ).trans (congrArg (fun k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ => (g.1.map (embAt B.embLL B.fields.emb τ) * k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ)) (congrFun (hY y) τ)).symm)
  rw [(hF u).eWz] at h
  have h' : B.embLL _ * φ ((I.perIn u I.mu0).tilC c) (frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y)) = _ * φ ((I.perIn u I.mu0).tilC c) y := h
  have hy : frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y) = y := by
    by_contra hne
    simp only [φ, if_neg hne, if_pos, mul_zero, mul_one] at h'
    exact Units.ne_zero _ h'.symm
  exact congrArg Units.val (eq_of_frMul (show B.fields.Tau from (I.rec7 l Z).eTau.symm 1) _ _ _ _ _ hy)

theorem crdN_stabM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → CarH H F → ∀ (u : B.Word) (h1 : 1 ≤ (I.rec7 l Z).R.m) (c : ((I.rec7 l Z).mem u).C.cls (I.rec7 l Z).R.m) (s : ((I.rec7 l Z).mem u).C.stab (I.rec7 l Z).R.m c) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 c s y) = ((I.stp u I.mu0 B.R.m).gam c.1 s.1).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F hF hC u h1 c s y
  obtain ⟨k, hk⟩ := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have e1 := hk.stab c s
  have e2 := (hC.carM u).st_eq c s
  have e3 : ∀ (β β' : H.Ch u (I.rec7 l Z).R.m) (h : H.chOf u (I.rec7 l Z).R.m c = β) (h' : H.chOf u (I.rec7 l Z).R.m c = β'),
      ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β).stabI ⟨c, h⟩ s).1 = ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β').stabI ⟨c, h'⟩ s).1 := by
    intro β β' h h'
    subst h
    subst h'
    rfl
  refine (co_symm_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y).trans ?_
  refine congrArg (fun k : GL (Fin (B.R.N B.R.m)) B.fields.E => k.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y) ?_
  rw [← e1]
  exact (congrArg _ (e3 _ _ rfl (chOf_m H u c))).trans e2.symm

theorem crdP_stabP : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u)) → CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (s : ((I.rec7 l Z).fm u).stabilizer₂ c) (x : (I.rec7 l Z).sp.X'.V), crdP (I.rec7 l Z) (Formalism.L2.Herm.stabPLinS (I.rec7 l Z) H A u c s x) = ((I.perIn u I.mu0).S'.gam c.1 s.1).1 *ᵥ crdP (I.rec7 l Z) x := by
  intro B X I l Z H F A hF hC u c s x
  have e1 := (hF u).what₂.stab c s
  have e2 := (hC.carP u).st_eq c s
  refine (co_symm_apply (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) _ x).trans ?_
  exact congrArg (fun k : GL (Fin (B.R.N B.R.m - 1)) B.fields.E => k.1 *ᵥ crdP (I.rec7 l Z) x) (e2.symm.trans e1)

theorem crdN_tilG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 y) = ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F A hC u c y
  rw [hC.ga u c]
  exact co_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y

theorem gam_ext : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (b : (I.perIn u I.mu0).S'.β) (g : (I.perIn u I.mu0).S'.G b), (∀ y, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ iXc (I.rec7 l Z) y = iXc (I.rec7 l Z) (((I.perIn u I.mu0).S'.gam b g).1 *ᵥ y)) ∧ ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ TC.z0 X u = TC.z0 X u := by
  intro B X I hOk hP l Z u b g
  have hi := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).2.2.1
  have ini : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iniH (N_m_succ B.R) (iXc (I.rec7 l Z) y) = y := fun y => by
    funext j
    exact (hi y _).trans (dif_pos j.2)
  have las : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iXc (I.rec7 l Z) y (Br.iL (N_m_succ B.R)) = 0 := fun y =>
    (hi y _).trans (dif_neg (lt_irrefl _))
  refine ⟨fun y => ext_vec (N_m_succ B.R) ?_ ?_, ext_vec (N_m_succ B.R) ?_ ?_⟩
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    exact (congrArg _ (ini _)).trans (ini _).symm
  · exact ((l.per u I.mu0).gam_last b g _).trans ((las _).trans (las _).symm)
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    have z : iniH (E := B.fields.E) (N_m_succ B.R) (TC.z0 X u) = 0 := by
      funext j
      exact if_neg (by have := j.2; show ¬ (j.1 + 1 = _); omega)
    exact (congrArg _ z).trans ((Matrix.mulVec_zero _).trans z.symm)
  · exact (l.per u I.mu0).gam_last b g _

theorem stabMap_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hOk hPins l Z H F hStd hCarH A hCarT u h1 c s
  have hF : ∀ u, I.StdF l Z u (F u) := fun u => (hStd u).1
  have hga := ga_eq_gam_mv I l Z H F hF u c
  have conj : ∀ v, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam _ (((I.rec7 l Z).fm u).stabMap c s).1).1 *ᵥ v) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) := by
    intro v
    show _ *ᵥ (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 (((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))⁻¹ * (I.perIn u I.mu0).ext c.1 s.1 *
          (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) = _
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ∀ y, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 _
      (((I.rec7 l Z).fm u).stabMap c s) (((A u).tilG c).1.symm y))) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
    intro y
    have hw : ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1.symm y) =
        crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
      rw [← crdN_tilG I l Z H F A hCarT u c, LinearEquiv.apply_symm_apply]
    rw [crdN_tilG I l Z H F A hCarT u c, crdN_stabM I l Z H F hF hCarH u h1, ← hw, hga]
    exact conj _
  have hiX : ∀ x, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl ((I.rec7 l Z).sp.iX' x) = iXc (I.rec7 l Z) (crdP (I.rec7 l Z) x) := by
    intro x
    simp [iXc, crdN, crdP]
  have hext := gam_ext I hOk hPins l Z u c.1 s.1
  refine ⟨fun x => ?_, ?_⟩
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, hiX, hiX, hext.1, crdP_stabP I l Z H F A hF hCarT u c s x]
    rfl
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, ← hCarT.z0 u]
    have hz : (F u).til.z0 = TC.z0 X u := funext fun j => (hF u).z0 j
    rw [hz, hext.2]

end GlobalTheory.Mem.Col2.HAt.Stab
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCont

open IsLocalRing

theorem continuous_of_le_comap {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (h : maximalIdeal A ≤ (maximalIdeal B).comap φ) : Continuous φ := by
  apply continuous_of_continuousAt_zero φ.toAddMonoidHom
  rw [isAdic_iff] at hA hB
  intro s hs
  simp only [map_zero] at hs
  obtain ⟨n, hn⟩ := hB.2 s hs
  have h1 : ((maximalIdeal A ^ n : Ideal A) : Set A) ∈ nhds (0 : A) :=
    (hA.1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.mem_map.2 (Filter.mem_of_superset h1 fun a ha => hn ?_)
  have : (maximalIdeal A ^ n).map φ ≤ maximalIdeal B ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 h) n
  exact this (Ideal.mem_map_of_mem φ ha)

theorem comap_maximalIdeal_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (maximalIdeal O).comap (algebraMap ℤ_[p] O) = maximalIdeal ℤ_[p] :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal O))

theorem p_mem_maximalIdeal {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : ((p : ℕ) : O) ∈ maximalIdeal O := by
  have hp : ((p : ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  rw [← comap_maximalIdeal_padicInt O] at hp
  simpa using hp

theorem le_comap_of_padicInt {p : ℕ} [Fact p.Prime] {A B : Type} [CommRing A] [IsLocalRing A] [Algebra ℤ_[p] A]
    [Module.Finite ℤ_[p] A] [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (φ : A →+* B)
    (hφ : ∀ z, φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[p] B z) : maximalIdeal A ≤ (maximalIdeal B).comap φ := by
  have hc : ((maximalIdeal B).comap φ).comap (algebraMap ℤ_[p] A) = maximalIdeal ℤ_[p] := by
    rw [Ideal.comap_comap, ← comap_maximalIdeal_padicInt B]
    congr 1
    exact RingHom.ext hφ
  haveI : ((maximalIdeal B).comap φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap ℤ_[p] A)
      (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance))
      ((maximalIdeal B).comap φ) (by rw [hc]; infer_instance)
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem continuous_of_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = q) {A B : Type} [CommRing A] [IsLocalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [IsLocalRing B]
    [Algebra ℤ_[q] B] [Module.Finite ℤ_[q] B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (maximalIdeal A)) (hB : IsAdic (maximalIdeal B)) (φ : A →+* B)
    (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap ℤ_[p] A z) = algebraMap ℤ_[q] B z') : Continuous φ := by
  subst hpq
  exact continuous_of_le_comap hA hB φ (le_comap_of_padicInt φ fun z => hφ z z HEq.rfl)

theorem continuous_algebraMap_padicInt {p : ℕ} [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] [TopologicalSpace O] [IsTopologicalRing O] (hO : IsAdic (maximalIdeal O)) :
    Continuous (algebraMap ℤ_[p] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[p] O) ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[p]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (p_mem_maximalIdeal O) n)

section Units

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_units {O : Type} [Monoid O] [TopologicalSpace O] (φ : Γ →* Oˣ)
    (h : Continuous fun g => (φ g : O)) : Continuous φ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have : (fun g => ((φ g)⁻¹ : Oˣ).val) = fun g => (φ g⁻¹ : O) := by
    funext g; rw [map_inv]
  rw [this]
  exact h.comp continuous_inv

theorem continuous_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B] (f : A →* B)
    (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

theorem continuous_of_isOpen_ker {N : Type} [Group N] [TopologicalSpace N] (φ : Γ →* N)
    (h : IsOpen (φ.ker : Set Γ)) : Continuous φ := by
  refine IsLocallyConstant.continuous fun s => ?_
  have e : φ ⁻¹' s = ⋃ x ∈ φ ⁻¹' s, (fun g => x⁻¹ * g) ⁻¹' (φ.ker : Set Γ) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, exists_prop]
    constructor
    · intro hg; exact ⟨g, hg, inv_mul_cancel _⟩
    · rintro ⟨x, hx, hxg⟩
      rw [inv_mul_eq_one] at hxg
      rwa [← hxg]
  rw [e]
  exact isOpen_biUnion fun x _ => h.preimage (continuous_const.mul continuous_id)

end Units

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem chiN_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  intro D M C hR X hS twC ψ0 hP htw hker i c
  have hadic : ∀ j w, IsAdic (maximalIdeal (OcC X j w)) := oc_adic X
  have htwc : ∀ j w, Continuous (twC j w) := fun j w =>
    continuous_of_heq (C.twI_l w) (D.ntw.twistBaseCoefficientRing_isAdic (C.twI w)) (hadic j w) (twC j w) (htw j w)
  have h1 : Continuous (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i)
      (C.sd (wOf (base M C hR X hS) i))) :=
    continuous_units _ (D.ntw.twistCharacterFamily_continuous _ _ _)
  have h2 : Continuous (psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)) :=
    continuous_of_isOpen_ker _ (hker _ _)
  have h3 : Continuous (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (htwc _ _)
  haveI : Fact (lOf (base M C hR X hS) i).Prime := ⟨D.what₂.places.resChar_prime _⟩
  letI : Algebra ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).algOc _ _
  haveI : Module.Finite ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i) := (base M C hR X hS).finOc _ _
  have h4 : Continuous (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom) :=
    continuous_unitsMap _ (continuous_algebraMap_padicInt _ (hadic _ _))
  have h5 := continuous_cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i)
  refine Units.continuous_val.comp ?_
  change Continuous fun g =>
    ((show (OOf (base M C hR X hS) i)ˣ from (Units.map (twC (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i)).toMonoidHom)
      (D.ntw.chi1 (C.twI (wOf (base M C hR X hS) i)) (Fam.NPC.jOf (base M C hR X hS) i) (C.sd (wOf (base M C hR X hS) i)) g)) *
      (show (OOf (base M C hR X hS) i)ˣ from psN X ψ0 hP (Fam.NPC.jOf (base M C hR X hS) i) (wOf (base M C hR X hS) i) g)) *
    (Units.map (algebraMap ℤ_[lOf (base M C hR X hS) i] (OOf (base M C hR X hS) i)).toMonoidHom
      (cycZ D.host.E D.nd.Om (lOf (base M C hR X hS) i) g)) ^ (-((c : ℤ) - 1))
  exact ((h3.comp h1).mul h2).mul ((h4.comp h5).zpow _)

end GlobalTheory.HeckeLocCont
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocN



def feSup {l : ℕ} [Fact l.Prime] (K L : Loc.FinExt l) : Loc.FinExt l :=
  ⟨K.1 ⊔ L.1, haveI := K.2; haveI := L.2; IntermediateField.finiteDimensional_sup _ _⟩

theorem osInt (D : D7) (B : LocBase0 D.host D.what₂) : OsInt B := fun j w y =>
  IsIntegrallyClosed.isIntegral_iff.1 <| by
    obtain ⟨p, hp, h0⟩ := D.O_int y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim (RingHom.comp _ _) ((B.ec j w).comp (algebraMap ℤ D.what₂.LL)), ← hom_eval₂, h0, map_zero]

theorem plGwDisj (D : D7) : PlGwDisj D := by
  have key : ∀ v v', D.naut.plGw 0 v ≠ D.naut.plGw 1 v' := fun v v' e => by
    have h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 0 v).asIdeal := D.naut.plGw_over 0 v
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 1 v').asIdeal := D.naut.plGw_over 1 v'
    rw [← e] at h1
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne).cast
    exact (D.naut.plGw 0 v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  intro k k' v v' e
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd e (key v v')
  · exact absurd e.symm (key v' v)
  · rfl

section Psi

variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)

theorem psN_spec (g : G D.host.E D.nd.Om) : algebraMap (OcC X j w) (FractionRing (OcC X j w)) (psN X ψ0 hP j w g : OcC X j w) =
    ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
  unitsLift_spec ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w) g


include hψ0 in
theorem psN_eq_one (g : G D.host.E D.nd.Om) : psN X ψ0 hP j w g = 1 ↔ ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) g = 1 := by
  rw [← Units.val_eq_one, ← map_eq_one_iff _ (IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))), psN_spec,
    map_eq_one_iff _ (ecC X j w).injective, ← map_eq_one_iff _ (C.embW w).injective, hψ0,
    map_eq_one_iff _ (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))), map_eq_one_iff _ (C.Oe_inj w),
    Units.val_eq_one]
  rfl

include hψ0 in
theorem psN_of_art {g : G D.host.E D.nd.Om} (h : D.ntw.art (C.twI w) (C.Q w) g = 1) : psN X ψ0 hP j w g = 1 := by
  rw [psN_eq_one hψ0, MonoidHom.comp_apply, h, map_one]

include hψ0 in
theorem psN_ord (g : G D.host.E D.nd.Om) : ∃ n : ℕ, psN X ψ0 hP j w g ^ (D.what₂.places.resChar w ^ n) = 1 := by
  obtain ⟨n, hn⟩ := D.ntw.RCG_l _ _ (D.ntw.art (C.twI w) (C.Q w) g)
  rw [C.twI_l, ← map_pow] at hn
  exact ⟨n, by rw [← map_pow]; exact psN_of_art hψ0 hP j w hn⟩

include hψ0 in
theorem psN_open : IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om)) :=
  Subgroup.isOpen_mono (H₁ := (D.ntw.art (C.twI w) (C.Q w)).ker) (fun _ hg => psN_of_art hψ0 hP j w hg) (D.ntw.art_cont _ _)

include hψ0 in
theorem psN_anti : AntiHom D.ntw.cc (psN X ψ0 hP j w) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact psN_of_art hψ0 hP j w (by rw [map_mul, D.ntw.art_anti _ _ g g' h, inv_mul_cancel])

include hψ0 in
theorem psN_ram (h : ∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) :
    RamExactly (psN X ψ0 hP j w) (↑(C.Q w) : Set (HeightOneSpectrum (𝓞 D.host.E))) := fun v A hA => by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    by_contra hv
    exact hne (psN_of_art hψ0 hP j w (D.ntw.art_unr _ _ v hv A hA σ hσ))
  · intro hv
    obtain ⟨σ, hσ, hne⟩ := h v hv A hA
    exact ⟨σ, hσ, fun e => hne ((psN_eq_one hψ0 hP j w σ).1 e)⟩

end Psi


end GlobalTheory.HeckeLocN
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCommute




theorem hLC_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  classical
  intro D M C hR hstd hgen hsplit j w v k v' k'
  by_cases h : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k
  swap
  · have : hLC (mt0 M) C.Q hR j w v k = 0 := by unfold hLC; rw [dite_eq_right h]
    rw [this]; exact Commute.zero_left _
  by_cases h' : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v' k'
  swap
  · have : hLC (mt0 M) C.Q hR j w v' k' = 0 := by unfold hLC; rw [dite_eq_right h']
    rw [this]; exact Commute.zero_right _
  obtain ⟨⟨h1, h2⟩, hg⟩ := h
  obtain ⟨-, hg'⟩ := h'
  obtain ⟨B, hB, hBv⟩ := hgen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hsplit v hg.1
  obtain ⟨s', ϖ', hc', hu'⟩ := hsplit v' hg'.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hsB' : s'.v ∉ B := hBv v' k' s' hg' hc'
  have hstd' := hstd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hB s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hcomm := hstd'.2.2.1 s' ϖ' k' hsB' hu' hg'.2.2.2.2.1 hg'.2.2.2.2.2
  rw [commute_iff_eq]
  ext x
  apply Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective
  apply (M (D.what₂.muTw w) j h1 h2).real_inj
  have hf : (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]; exact LinearMap.mem_range_self _ _
  have e1 := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu
  have e2 := hLC_spec (mt0 M) C.Q hR j w v' k' h1 h2 hg' s' ϖ' hc' hu'
  simp only [Module.End.mul_apply]
  change (mt0 M (D.what₂.muTw w) j h1 h2).real _ = (mt0 M (D.what₂.muTw w) j h1 h2).real _
  rw [e1, e2, e2, e1]
  exact hcomm _ hf

end GlobalTheory.HeckeLocCommute
end
end
