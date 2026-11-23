module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle349
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle353
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
public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle337
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Mathlib.Basic.PEquiv

@[expose] public section

section



open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

theorem _root_.GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  first | exact @GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | exact GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | (intros; apply GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section
namespace GlobalTheory.Pass.LocDual.Summand

theorem exists_left_inv {K : Type} [Field K] {Γ : Type} [Group Γ] {n k : ℕ}
    (A : Γ → Matrix (Fin n) (Fin n) K) (j : (Fin k → K) →ₗ[K] (Fin n → K)) (hinj : Function.Injective j)
    (W' : Submodule K (Fin n → K)) (hc : IsCompl (LinearMap.range j) W')
    (hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j)
    (hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W') :
    ∃ Bl : (Fin n → K) →ₗ[K] (Fin k → K), (∀ u, Bl (j u) = u) ∧
      ∀ g v, j (Bl ((A g).mulVec v)) = (A g).mulVec (j (Bl v)) := by
  let e := LinearEquiv.ofInjective j hinj
  let P := Submodule.linearProjOfIsCompl (LinearMap.range j) W' hc
  have hjB : ∀ v, j ((e.symm.toLinearMap ∘ₗ P) v) = (P v : Fin n → K) := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply (P v))
    simpa [e, LinearEquiv.ofInjective_apply] using this
  have hP : ∀ v, ∀ a ∈ LinearMap.range j, ∀ b ∈ W', v = a + b → (P v : Fin n → K) = a := by
    intro v a ha b hb hv
    subst hv
    have h1 : P a = ⟨a, ha⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨a, ha⟩
    have h2 : P b = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨b, hb⟩
    rw [map_add (f := _), Submodule.coe_add, h1, h2]
    simp
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_⟩
  · intro u
    apply hinj
    rw [hjB]
    exact hP _ _ ⟨u, rfl⟩ 0 W'.zero_mem (by simp)
  · intro g v
    have hv : v ∈ LinearMap.range j ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hjB, hjB, hP (a + b) a ha b hb rfl, hP _ _ (hW g a ha) _ (hW' g b hb) (Matrix.mulVec_add _ _ _)]

theorem loc_eq (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (Br.toLLK (D.nbr i w hw)) := by
  refine Matrix.ext fun a b => ?_
  change (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) =
    Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b))
  rw [Br.toLLK_alg]
  rfl

theorem twist_eq (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (g : GE D.nd) :
    mapM (toK D.nd i) (rTwO D.nd i r x) g =
      toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) •
        ((mapRep (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) (r x) g : GL (Fin D.R.nV) (FractionRing (D.nd.O i))) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) := by
  refine Matrix.ext fun a b => ?_
  change toK D.nd i (((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * ((r x g : GL _ _) : Matrix _ _ _) a b) =
    toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * toK D.nd i (((r x g : GL _ _) : Matrix _ _ _) a b)
  exact map_mul _ _ _

end GlobalTheory.Pass.LocDual.Summand


open GlobalTheory.Pass.LocDual.Summand in


theorem GlobalTheory.Pass.LocDual.isSummandTw_locU : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsSummandTw i w hw r Xs (locU i w hw M hSub.1) := by
  intro D i r hr Xs w hw k M hSub
  obtain ⟨x, hx, j, hinj, hj⟩ := hSub.2
  let K := FractionRing (D.nd.O i)
  let A : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g => mapM (toK D.nd i) (rTwO D.nd i r x) g
  let Rm : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g =>
    ((mapRep (algebraMap (D.nd.O i) K) (r x) g : GL (Fin D.R.nV) K) : Matrix (Fin D.R.nV) (Fin D.R.nV) K)
  let c : GE D.nd → Kˣ := fun g => Units.map (toK D.nd i).toMonoidHom ((chiU D.nd i 1)⁻¹ g)
  have hA : ∀ g, A g = ((c g : Kˣ) : K) • Rm g := fun g => twist_eq D i r x g
  have hR : ∀ g v, (Rm g).mulVec v = (((c g)⁻¹ : Kˣ) : K) • (A g).mulVec v := by
    intro g v
    rw [hA, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hWinv : IsInv (mapRep (algebraMap (D.nd.O i) K) (r x)) (LinearMap.range j) := by
    rintro g _ ⟨u, rfl⟩
    change (Rm g).mulVec (j u) ∈ LinearMap.range j
    rw [hR, ← hj]
    exact ⟨(((c g)⁻¹ : Kˣ) : K) • (mapM (toK D.nd i) M g).mulVec u, by rw [map_smul]⟩
  obtain ⟨W', hW'inv, hcompl⟩ := (hr x).2.1 (LinearMap.range j) hWinv
  have hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨_, hj g u⟩
  have hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W' := by
    intro g v hv
    rw [hA, Matrix.smul_mulVec]
    exact W'.smul_mem _ (hW'inv g v hv)
  obtain ⟨Bl, hBj, hcomm⟩ := exists_left_inv A j hinj W' hcompl hW hW'

  let J : Matrix (Fin D.R.nV) (Fin k) K := LinearMap.toMatrix' j
  let B : Matrix (Fin k) (Fin D.R.nV) K := LinearMap.toMatrix' Bl
  have hJv : ∀ v, J.mulVec v = j v := fun v => LinearMap.toMatrix'_mulVec j v
  have hBv : ∀ v, B.mulVec v = Bl v := fun v => LinearMap.toMatrix'_mulVec Bl v
  have hBJ : B * J = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hJv, hBv, hBj,
      Matrix.toLin'_one, LinearMap.id_apply]
  have hPA : ∀ g, J * B * A g = A g * (J * B) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv, hBv, hcomm]
  have hJM : ∀ g, J * mapM (toK D.nd i) M g = A g * J := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv]
    exact hj g v
  let f := Br.toLLK (D.nbr i w hw)
  let JL : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw) := J.map f
  let BL : Matrix (Fin k) (Fin D.R.nV) (Br.LL D.nbr i w hw) := B.map f
  let PL : Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) := JL * BL
  have hBJL : BL * JL = 1 := by
    change B.map f * J.map f = 1
    rw [← Matrix.map_mul, hBJ, Matrix.map_one f (map_zero f) (map_one f)]
  have hPJ : PL * JL = JL := by
    change JL * BL * JL = JL
    rw [Matrix.mul_assoc, hBJL, Matrix.mul_one]
  have hloc : ∀ g, Br.loc D.nbr i w hw (rTwO D.nd i r x) g = (A (decS D.nd w (Br.iota D.nbr i w hw g))).map f :=
    fun g => loc_eq D i w hw _ g
  have hPL : ∀ g, PL * Br.loc D.nbr i w hw (rTwO D.nd i r x) g = Br.loc D.nbr i w hw (rTwO D.nd i r x) g * PL := by
    intro g
    rw [hloc]
    have := congrArg (fun Z => Z.map f) (hPA (decS D.nd w (Br.iota D.nbr i w hw g)))
    simp only [Matrix.map_mul] at this
    exact this
  refine ⟨1, fun _ => ⟨x, hx⟩, (LinearMap.pi fun _ => Matrix.mulVecLin JL : (Fin k → Br.LL D.nbr i w hw) →ₗ[Br.LL D.nbr i w hw] (Fin 1 → Fin D.R.nV → Br.LL D.nbr i w hw)), ?_, ?_, ?_⟩
  · show Function.Injective (fun (v : Fin k → Br.LL D.nbr i w hw) (_ : Fin 1) => JL.mulVec v)
    intro v v' h
    have h1 := congrArg (fun z => BL.mulVec (z 0)) h
    change BL.mulVec (JL.mulVec v) = BL.mulVec (JL.mulVec v') at h1
    simp only [Matrix.mulVec_mulVec, hBJL, Matrix.one_mulVec] at h1
    exact h1
  · show ∀ (g : Br.G D.nbr i w hw) (v : Fin k → Br.LL D.nbr i w hw), (fun (_ : Fin 1) => JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v)) =
      fun (_ : Fin 1) => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    intro g v
    funext b
    change JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v) = (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    simp only [Matrix.mulVec_mulVec]
    rw [hloc, loc_eq]
    change Matrix.mulVec (J.map f * (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map f) v = _
    rw [← Matrix.map_mul, hJM, Matrix.map_mul]
  · refine ⟨LinearMap.ker (LinearMap.pi fun b => (Matrix.mulVecLin PL).comp (LinearMap.proj b)), ?_, ?_⟩
    · intro g u hu
      have hu' : ∀ b, PL.mulVec (u b) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
      refine LinearMap.mem_ker.mpr (funext fun b => ?_)
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
      change PL.mulVec ((Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (u b)) = 0
      rw [Matrix.mulVec_mulVec, hPL, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_zero]
    · constructor
      · rw [Submodule.disjoint_def]
        rintro u ⟨(v : Fin k → Br.LL D.nbr i w hw), rfl⟩ hu
        have hu' : ∀ b, PL.mulVec (JL.mulVec v) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
        funext b
        change JL.mulVec v = 0
        rw [← hPJ, ← Matrix.mulVec_mulVec]
        exact hu' b
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        refine Submodule.mem_sup.mpr ⟨fun _ => PL.mulVec (u 0), ⟨BL.mulVec (u 0), ?_⟩, fun b => u b - PL.mulVec (u 0), ?_, ?_⟩
        · funext b
          change JL.mulVec (BL.mulVec (u 0)) = (JL * BL).mulVec (u 0)
          exact Matrix.mulVec_mulVec _ _ _
        · refine LinearMap.mem_ker.mpr (funext fun b => ?_)
          simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Subsingleton.elim b 0]
          change (JL * BL).mulVec (u 0) - (JL * BL * (JL * BL)).mulVec (u 0) = 0
          rw [Matrix.mul_assoc JL BL, ← Matrix.mul_assoc BL, hBJL, Matrix.one_mul, sub_self]
        · funext b
          change PL.mulVec (u 0) + (u b - PL.mulVec (u 0)) = u b
          exact add_sub_cancel _ _
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType.RestrictionTwo

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a : ℕ) (y : Gn p (a + 1)) :
    StdBlock a y ↔ InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · rw [h i j (by omega)]
      have : i ≠ j := fun e => by rw [e] at hi; omega
      simp [this]
    · ext i j
      have hi : (i : ℕ) < a + 1 := by omega
      have hj : (j : ℕ) < a + 1 := by omega
      have := h ⟨i, hi⟩ ⟨j, hj⟩ (by first | omega | simp | (simp; omega))
      simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this ⊢
      exact this
  · rintro ⟨h1, h2⟩ i j hij
    have hj : (j : ℕ) < a := by omega
    by_cases hi : (i : ℕ) < a
    · have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      have hi' : (i : ℕ) < a + 1 := by omega
      have hj' : (j : ℕ) < a + 1 := by omega
      simp only [tl, entN, hi', hj', and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this
      simp only [Fin.ext_iff]
      exact this
    · have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rw [if_neg hne]
      exact h1 i j hj (by omega)

theorem det_eq_of_stdBlock (a : ℕ) (y : Gn p (a + 1)) (h : StdBlock a y) :
    Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det (toG (br a 1 (y : Mt p (a + 1)))) := by
  obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 h
  rw [GlobalTheory.GLq.LabelDet.det_par a 1 y h1, h2, GlobalTheory.GLq.LabelDet.toG_one, map_one, one_mul]

theorem br_eq_iff (a : ℕ) (y : Gn p (a + 1)) (h : InPar a (y : Mt p (a + 1))) (x : Gn p 1) :
    br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) ↔ x = toG (br a 1 (y : Mt p (a + 1))) := by
  have hd := GlobalTheory.GLq.LabelDet.det_inPar a 1 _ h
  have h0 : (tl a (y : Mt p (a + 1))).det * (br a 1 (y : Mt p (a + 1))).det ≠ 0 := hd ▸ y.det_ne_zero
  have hu : IsUnit (br a 1 (y : Mt p (a + 1))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (right_ne_zero_of_mul h0))
  have hv : ((toG (br a 1 (y : Mt p (a + 1))) : Gn p 1) : Mt p 1) = br a 1 (y : Mt p (a + 1)) := by
    unfold toG; rw [dif_pos hu]; exact IsUnit.unit_spec hu
  constructor
  · intro e; apply Units.ext; rw [hv, e]
  · intro e; rw [e, hv]

theorem sum_res_eq (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : Gn p (a + 1) → ℂ) :
    ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x =
      ((p : ℂ) ^ a)⁻¹ * stdTrace a θ α := by
  rw [stdTrace, Finset.mul_sum]
  unfold res
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hs : StdBlock a y
  · obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 hs
    rw [if_pos hs]
    have e : ∀ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * (((p : ℂ) ^ (a * 1))⁻¹ *
        if InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = ((1 : Gn p a) : Mt p a) ∧
          br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) then α y else 0) =
        if x = toG (br a 1 (y : Mt p (a + 1))) then
          ((p : ℂ) ^ a)⁻¹ * ((((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * α y) else 0 := by
      intro x
      by_cases hx : x = toG (br a 1 (y : Mt p (a + 1)))
      · rw [if_pos ⟨h1, by rw [h2, Units.val_one], (br_eq_iff a y h1 x).2 hx⟩, if_pos hx, det_eq_of_stdBlock a y hs, ← hx,
          MonoidHom.inv_apply, Nat.mul_one]
        ring
      · rw [if_neg (fun h => hx ((br_eq_iff a y h1 x).1 h.2.2)), if_neg hx, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_eq']
    simp
  · rw [if_neg hs, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg, mul_zero, mul_zero]
    rintro ⟨h1, h2, -⟩
    exact hs ((stdBlock_iff a y).2 ⟨h1, by rw [h2, Units.val_one]⟩)

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 →
    ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ
      (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  intro p _ a θ α hα hne
  have key : ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x ≠ 0 := by
    rw [sum_res_eq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) hne
  obtain ⟨σ, hσ, h⟩ := (GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv p a α hα θ⁻¹).1 key
  exact ⟨σ, hσ, by simpa only [inv_inv] using h⟩

end GlobalTheory.LevelType.RestrictionTwo
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_map_of_typeVec (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL n F) W) (ρ : FDRep ℂ (GL n (ZMod p))) (y : W) :
    resCard F = p → TypeVec π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y → ∃ φ : ρ →ₗ[ℂ] W, φ ≠ 0 ∧
      ∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, π h (φ w) = φ (ρ.ρ g w) := by
  intro hp hy
  obtain ⟨h1, ℓ, hℓ, h0⟩ := hy
  let Φ : Module.Dual ℂ ρ → (ρ →ₗ[ℂ] W) := fun μ =>
    ∑ g : GL n (ZMod p), LinearMap.smulRight (μ ∘ₗ ρ.ρ g⁻¹) (π (ℓ g) y)
  have hΦ : ∀ μ w, Φ μ w = ∑ g, μ (ρ.ρ g⁻¹ w) • π (ℓ g) y := by
    intro μ w
    simp [Φ, LinearMap.sum_apply]
  have heq : ∀ μ (g₀ : GL n (ZMod p)) (h : GL n F), IsLift g₀ h → ∀ w, π h (Φ μ w) = Φ μ (ρ.ρ g₀ w) := by
    intro μ g₀ h H w

    rw [hΦ, hΦ, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, IsLift.apply_eq hp h1 (H.mul hp (hℓ g)) (hℓ _)]
    simp [mul_inv_rev, map_mul, Module.End.mul_apply]
  by_contra hne
  have hz : ∀ μ, Φ μ = 0 := fun μ => by
    by_contra e
    exact hne ⟨_, e, heq μ⟩
  apply h0
  let b := Module.finBasis ℂ ρ
  have key : ∑ g, LinearMap.trace ℂ ρ (ρ.ρ g⁻¹) • π (ℓ g) y = 0 := by
    have : ∑ i, Φ (b.coord i) (b i) = 0 := by simp [hz]
    rw [← this]
    simp_rw [hΦ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff, mul_smul]
  rw [← Finset.smul_sum, key, smul_zero]

end GlobalTheory.LevelType
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ, (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧ ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | exact GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | (intros; apply GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.dualLattice_restrictScalars_traceForm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  first | exact @GlobalTheory.DualLatDescent.dualLat_resQ | exact GlobalTheory.DualLatDescent.dualLat_resQ | (intros; apply GlobalTheory.DualLatDescent.dualLat_resQ <;> assumption)
end
