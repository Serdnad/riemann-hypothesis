module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle002
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConst
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle021
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle022
public import Development.WeilBound.ThetaLifts.SmallCones.SoStab
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtExA
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem thConst_of' (hL : LocDist) (hG : GoodNe) (hC : ConstOfGood) (hF : Factor) (hM : MatchEx) (hT : ThetaBasic) (hD : KDecay)
    (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : PositivityTheory.ThKEst.EpsOf) (h3 : PositivityTheory.ThKEst.FinVolU) (h4 : PositivityTheory.ThKF.Unimod) : ThConst :=
  thConst_of hL hG hC hF hM hT hD h1 h2 h3 h4 TC.splitModel PositivityTheory.KCo.so_statement

end GlobalTheory.ThK.Dbl

end
end

section

namespace GlobalTheory.ThK.Dbl

theorem pairsIrr : PairsIrr := pairsIrr_of_arch PositivityTheory.ThKF.A.archOp

theorem pairsStable : PairsStable :=
  pairsStable_of (PositivityTheory.ThKEnd.Grp.matchStab_of PositivityTheory.ThKF.A.archOp PositivityTheory.ThKF.pureAct PositivityTheory.ThKEst.level PositivityTheory.ThKCT.soStab_of)

end GlobalTheory.ThK.Dbl
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open PositivityTheory.ThKH.Iwas Hgt
open Formalism.UG (bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

theorem trace_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (hv : PsiUnr ψ v) {z : E} (hz : InD z) :
    algebraMap F (Fv F v) (Algebra.trace F E z) ∈ v.adicCompletionIntegers F := by
  refine (hv _).1 fun y hy => ?_
  have := GlobalTheory.LatVacArith.psi_int hψ (Algebra.trace F E z) (fun a => ?_) (singleFin v y) (fun u => ?_)
  · refine Eq.trans (congrArg (fun t : Af F => ψ (pairA F 0 t)) (GlobalTheory.AdelicU.af_ext fun u => ?_)) this
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v _) = _
    rw [map_mul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u)]
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, evalV_singleFin_self, mul_comm]; rfl
    · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]
  · obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (hz (algebraMap (𝓞 F) (𝓞 E) a))
    refine ⟨k, Eq.trans ?_ hk.symm⟩
    rw [← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def]
    rfl
  · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (singleFin v y) ∈ _
    by_cases e : u = v
    · subst e; rwa [evalV_singleFin_self]
    · rw [evalV_singleFin_ne e]; exact zero_mem _

theorem add_conj (h : IsCMExt F E σ) (z : E) : z + σ z = algebraMap F E (Algebra.trace F E z) := by
  classical
  have := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := z)
  let τ := IsScalarTower.toAlgHom F E (AlgebraicClosure E)
  apply (τ : E →+* AlgebraicClosure E).injective
  rw [show (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} from
    Finset.ext fun ρ => by simpa using eq_or_eq_comp_conj h τ ρ, Finset.sum_pair (comp_conj_ne h τ).symm] at this
  rw [map_add (f := _)]
  exact this.symm.trans (τ.commutes _).symm

theorem inD_mem {B : Base F E} (hB : B.IsGood σ) {w : Pl E} (hw : Formalism.UG.IsInertAt F E v w) {z : E} (hz : InD z) :
    inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  set Z := inclR (F := F) (Fv F v) z
  have key : ∀ y ∈ intLoc F E v, y * Z + sigR _ σ (y * Z) ∈ intLoc F E v := fun y hy => by
    refine intLoc_induction (p := fun y => y * Z + sigR _ σ (y * Z) ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun _ _ h h' => by convert add_mem h h' using 1; simp only [add_mul, map_add (f := _)]; ring)
      (fun _ h => by convert neg_mem h using 1; simp only [neg_mul, map_neg]; ring) hy
    convert tmul_mem_intLoc (mul_mem ha (trace_mem hB.std (hB.inert v w hw).2.2 (hz.mul x))) 1 using 1
    rw [show a ⊗ₜ[F] (x : E) * Z = a ⊗ₜ[F] (z * x) from (Algebra.TensorProduct.tmul_mul_tmul a 1 _ z).trans (by rw [mul_one, mul_comm])]
    change a ⊗ₜ[F] (z * x) + a ⊗ₜ[F] σ (z * x) = _
    rw [← TensorProduct.tmul_add, add_conj hB.cm, mul_comm a, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]
    rfl
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, -, -, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hB.cm hw hc
  obtain ⟨y, rfl⟩ := (toCompl_bijective hw hu).2 x
  have hy := (mem_intLoc_iff hw hu y).2 hx
  have h1 := (mem_intLoc_iff hw hu _).1 (sub_mem (mul_mem (sigR_mem_intLoc σ hy) (key 1 (one_mem _))) (key y hy))
  rw [show sigR _ σ y * (1 * Z + sigR _ σ (1 * Z)) - (y * Z + sigR _ σ (y * Z)) = (sigR _ σ y - y) * Z by
    simp only [one_mul, map_mul]; ring, map_mul, map_sub, ← hc] at h1
  refine (mem_intLoc_iff hw hu _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  rwa [map_mul, hx1, one_mul] at h2


variable (σ v) in
def Uni (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (Fv F v ⊗[F] E)) : Prop :=
  Int (intLoc F E v) (g.1ᵀ * J.map (inclR (F := F) (Fv F v)) * g.1.map (sigR _ σ)) ∧
    ∃ G', Int (intLoc F E v) G' ∧ G' * (g.1ᵀ * J.map (inclR (F := F) (Fv F v)) * g.1.map (sigR _ σ)) = 1

theorem exists_loc {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (v : Pl F) : ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)) (l : (Fv F v ⊗[F] E)ˣ),
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := by
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  haveI hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  let ι := inclR (F := F) (E := E) (Fv F v)
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  have eG : (bc ι P).1ᵀ * Y.J.map ι * (bc ι P).1.map (sigR _ σ) = G.map ι := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]; rfl
  have one : ∀ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 → G'.map ι * G.map ι = 1 := fun G' h => by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  suffices h : ∃ l : (Fv F v ⊗[F] E)ˣ, Int (intLoc F E v) (((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι) ∧
      ∃ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 ∧ Int (intLoc F E v) ((l.1 * sigR _ σ l.1) • G'.map ι) by
    obtain ⟨l, a1, G', a2, a3⟩ := h
    have e : (l⁻¹ • bc ι P).1ᵀ * Y.J.map ι * (l⁻¹ • bc ι P).1.map (sigR _ σ) = ((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι := by
      rw [← eG, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul]
      congr 1
      exact Matrix.ext fun i j => map_mul (sigR (Fv F v) σ) (l⁻¹).1 _
    refine ⟨bc ι P, l⁻¹ • bc ι P, l, Frames.frame_of_rational P h1 h2, (smul_inv_smul l _).symm, e ▸ a1, _, a3, ?_⟩
    rw [e, Matrix.smul_mul, Matrix.mul_smul, one G' a2, smul_smul, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul, one_smul]
  rcases hY with h | h
  · obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
      isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2
    exact ⟨1, fun i j => by simpa using (b1 i j).mem, G', b0, fun i j => by simpa using (b2 i j).mem⟩
  obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
  obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2
  rw [← hG] at b0 b1
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have s1 : (G.map σ)ᵀ = -G := (gram_sym (σ : E →+* E) hσ (ε := -1)
      (Matrix.ext fun i j => (h.skew i j).trans (neg_one_mul _).symm) P.1).trans (neg_one_smul _ _)
    have s2 : (G'.map σ)ᵀ = -G' := by
      have e : (G.map σ)ᵀ * (G'.map σ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        change (G'.map (σ : E →+* E) * G.map (σ : E →+* E))ᵀ = 1
        rw [← Matrix.map_mul, b0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
      rw [← Matrix.one_mul (G'.map σ)ᵀ, ← b0, Matrix.mul_assoc, ← neg_neg G, ← s1, Matrix.neg_mul, e]; simp
    let u := (splitAlgEquiv hc τ).symm
    have fin : ∀ (d : E) (X : Matrix (Fin n) (Fin n) E), (X.map σ)ᵀ = -X → (∀ i j, LocInt v (d * X i j)) →
        Int (intLoc F E v) ((u (τ d, 1) * sigR _ σ (u (τ d, 1))) • X.map ι) := fun d X hX hd i j => by
      have q : ∀ i j, τ d * τ (X i j) ∈ v.adicCompletionIntegers F := fun i j => by
        simpa [inclR] using splitProj_mem τ (hd i j).mem
      have q' : σ (X i j) = -X j i := congrFun (congrFun hX j) i
      refine (mem_intLoc_iff_split hc τ).2 ⟨?_, ?_⟩
      · simpa [u, ι, inclR, ← splitProj_comp] using q i j
      · simpa [u, ι, inclR, splitProj_comp_sigR hc, q'] using q j i
    have e : u (τ δ, 1) * u (τ δ⁻¹, 1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ d0, map_one, mul_one]; exact map_one u
    exact ⟨⟨_, _, e, (mul_comm _ _).trans e⟩, fin _ _ s1 b1, G', b0, fin _ _ s2 b2⟩
  · have i1 := inD_mem hB hw d1
    have i2 := (d2 1 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))).mem
    refine ⟨1, fun i j => ?_, G', b0, fun i j => ?_⟩
    · simpa [← map_mul, d0] using mul_mem i1 (b1 i j).mem
    · simpa [← map_mul, d0] using mul_mem i2 (b2 i j).mem

theorem ae_locInt (z : E) : ∀ᶠ v : Pl F in cofinite, LocInt v z := by
  obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple
  refine (Ideal.finite_factors (I := Ideal.span {(m : 𝓞 F)}) (by simpa using hm)).subset fun v hv => by_contra fun h => hv ?_
  exact ⟨m, fun k => h (Ideal.dvd_span_singleton.2 k), ⟨_, hi⟩, by simp⟩

theorem exists_ad {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (c : InfinitePlace F → GL (Fin n) ℂ) : ∃ a g : GL (Fin n) (AE F E), GlobalTheory.AdelicU.IsLatticeFrame Y.L a ∧
      (∀ v, (∃ l : (Fv F v ⊗[F] E)ˣ, (bc (compFin F E v) a).1 = l.1 • (bc (compFin F E v) g).1) ∧ Uni σ v Y.J (bc (compFin F E v) g)) ∧
      ∀ w, bc (piInf (B.emb w)) g = c w := by
  classical
  haveI hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨S, hS⟩ := Frames.exists_finset_latLoc_eq (F := F) Y.L
  have h0 : ∀ᶠ v : Pl F in cofinite, v ∉ S ∧ ∀ i j, LocInt v (Y.J i j) ∧ LocInt v (Y.J⁻¹ i j) :=
    S.eventually_cofinite_notMem.and (eventually_all.2 fun i => eventually_all.2 fun j => (ae_locInt _).and (ae_locInt _))
  have key : ∀ v : Pl F, ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)), (v ∉ Set.Finite.toFinset h0 → a = 1 ∧ g = 1) ∧ ∃ l : (Fv F v ⊗[F] E)ˣ,
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := fun v => by
    by_cases hv : v ∈ Set.Finite.toFinset h0
    · obtain ⟨a, g, h⟩ := exists_loc hB hY hJ v
      exact ⟨a, g, fun h => absurd hv h, h⟩
    · have hv' := not_not.1 (mt (Set.Finite.mem_toFinset h0).2 hv)
      refine ⟨1, 1, fun _ => ⟨rfl, rfl⟩, 1, fun y => by simpa using hS v hv'.1 y, (one_smul _ _).symm, ?_⟩
      rw [Uni, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      refine ⟨fun i j => (hv'.2 i j).1.mem, Y.J⁻¹.map (inclR (F := F) (Fv F v)), fun i j => (hv'.2 i j).2.mem, ?_⟩
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  choose a g h1 l h2 h3 h4 using key
  let e := fun w => RingEquiv.ofBijective _ (infEmb_bijective hB.cm (B.emb w))
  obtain ⟨a', ha, -⟩ := Frames.exists_GL_of_components _ a (fun v hv => (h1 v hv).1) fun _ => 1
  obtain ⟨g', hg, hg'⟩ := Frames.exists_GL_of_components _ g (fun v hv => (h1 v hv).2) fun w => bc (e w).symm.toRingHom (c w)
  refine ⟨a', g', fun v y => ha v ▸ h2 v y, fun v => ?_, fun w => Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [ha, hg]; exact ⟨⟨_, h3 v⟩, h4 v⟩
  · exact (congrArg (fun x => e w (x.1 i j)) (hg' w)).trans ((e w).apply_symm_apply _)

end GlobalTheory.ThK.Dbl.Frame

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped Matrix TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.WeilM Hgt

theorem hgtEx_of (hK : Stab2Cpt) : HgtEx := fun F E _ _ _ _ _ σ B n Y r s hB hY =>
  hgtEx_core hB hY (hK F E σ B n Y r s hB hY _ (isStab2_stab2 B))

theorem Hgt.graph_alg {S ι : Type} [CommRing S] [Fintype ι] [DecidableEq ι] (c : S →+* S) {g g' t t' : Matrix ι ι S} (hg : g * g' = 1)
    (ht : t' = g' * t) (hd : g'.det * c g'.det = 1) :
    (t.det * c t.det) • g = c t'.det • (t * t'.adjugate) ∧ (t.det * c t.det) • g' = c t.det • (t' * t.adjugate) := by
  constructor
  · have e : t = g * t' := by rw [ht, ← Matrix.mul_assoc, hg, Matrix.one_mul]
    conv_rhs => rw [e, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [ht, Matrix.det_mul, map_mul]
    congr 1
    linear_combination (-(t.det * c t.det)) * hd
  · rw [ht, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

theorem hgtInt_of (hC : Stab2Cpt) : HgtInt := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K a e hK ha he μ hμ
  have := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := t2Space_adeleRing' (F := F)
  have := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  have cK := hC F E σ B n Y r s hB hY K hK
  obtain ⟨⟨K', a', hK', ha', ca, a0⟩, e', ce, he'⟩ := hgtEx_of hC F E σ B n Y r s hB hY
  obtain rfl : K = K' := Subgroup.ext fun k => (hK k).trans (hK' k).symm
  obtain rfl : a = a' := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha'.val p t hp k hk]
  obtain rfl : e = e' := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he x.1 x.2).trans (he' x.1 x.2).symm))
  have cc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  let T : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₁
  let T' : G2 σ Y → Matrix (Fin n) (Fin n) (AE F E) := fun k => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)).toRows₂
  have cm : Continuous fun k : G2 σ Y => (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) :=
    ((Units.continuous_val.comp continuous_subtype_val).comp continuous_inv).matrix_mul continuous_const
  have cT : Continuous T := cm.matrix_submatrix _ _
  have cT' : Continuous T' := cm.matrix_submatrix _ _
  have : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
  let c := (Module.Free.chooseBasis (AF F) (Matrix (Fin n) (Fin n) (AE F E))).equivFun
  obtain ⟨R, C, b, h1, h2, h3, h4⟩ := count_ad (E := E) hB.cm.1 c (IsModuleTopology.continuous_of_linearMap c.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap) (UG (cA σ) (incM F Y.J))
    (isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map cc)) continuous_const)
    ((cK.image ((cc.comp cT'.matrix_det).smul (cT.matrix_mul cT'.matrix_adjugate))).union
      (cK.image ((cc.comp cT.matrix_det).smul (cT'.matrix_mul cT.matrix_adjugate))))
    (cK.image (continuous_norm_tens.comp cT.matrix_det)) μ
  have key : ∀ g : UA σ Y.J, ∃ k ∈ K, ∃ t : GL (Fin n) (AE F E), a (e (1, g)) = absE F E (Matrix.GeneralLinearGroup.det t) ∧
      T k = t.1 ∧ T' k = mat g⁻¹ * t.1 := fun g => by
    obtain ⟨p, t, hp, k, hk, h⟩ := ha.iwa (e (1, g))
    have e1 : k⁻¹ = e (1⁻¹, g⁻¹) * p := by rw [← Prod.inv_mk, map_inv, h]; group
    have hp' : (mat2 p * diagCols (E := AE F E) (Fin n)) = (diagCols (E := AE F E) (Fin n) * t.1) := hp
    have e2 : (mat2 k⁻¹ * diagCols (E := AE F E) (Fin n)) = Matrix.fromRows t.1 (mat g⁻¹ * t.1) := by
      rw [e1, show mat2 (e (1⁻¹, g⁻¹) * p) = mat2 (e (1⁻¹, g⁻¹)) * mat2 p from rfl, Matrix.mul_assoc, hp', he, inv_one,
        show mat (1 : UA σ Y.J) = 1 from rfl, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
      simp
    exact ⟨k, hk, t, by rw [h, ha.val p t hp k hk], congrArg Matrix.toRows₁ e2, congrArg Matrix.toRows₂ e2⟩
  refine integrable_of_count μ (ca.comp (ce.comp (Continuous.prodMk_right 1))).measurable (fun g => a0 _) (R := R) h1 (fun g => ?_)
    h2 b fun j => (measure_mono fun g hg => ?_).trans (h4 j)
  · obtain ⟨k, hk, t, e1, e2, -⟩ := key g
    exact e1.trans_le (h3 _ ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩)
  · obtain ⟨k, hk, t, e1, e2, e3⟩ := key g
    have hd : (mat g⁻¹).det * (cA σ).toRingHom (mat g⁻¹).det = 1 := by
      have h := congrArg Matrix.det (show (mat g⁻¹)ᵀ * incM F Y.J * (mat g⁻¹).map (cA σ) = incM F Y.J from (g⁻¹).2)
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show ((mat g⁻¹).map (cA σ)).det = (cA σ).toRingHom (mat g⁻¹).det from ((cA σ).toRingHom.map_det _).symm] at h
      refine (isUnit_det_JR (R := AF F) (det_ne hY)).mul_left_cancel ?_
      change (incM F Y.J).det * _ = (incM F Y.J).det * _
      linear_combination h
    obtain ⟨q1, q2⟩ := Hgt.graph_alg (cA σ).toRingHom (g := mat g) g.1.mul_inv e3 hd
    have q : ∀ X : Matrix (Fin n) (Fin n) (AE F E), Algebra.norm (AF F) t.1.det • X = (t.1.det * (cA σ).toRingHom t.1.det) • X :=
      fun X => by rw [← algebraMap_smul (AE F E), algebraMap_norm_eq hB.cm, ← cA_eq]; rfl
    refine ⟨Matrix.GeneralLinearGroup.det t, ⟨k, hk, congrArg (fun x => Algebra.norm (AF F) (Matrix.det x)) e2⟩, e1 ▸ hg,
      .inl ⟨k, hk, Eq.symm ((q _).trans (q1.trans ?_))⟩, .inr ⟨k, hk, Eq.symm ((q _).trans (q2.trans ?_))⟩⟩ <;> rw [← e2] <;> rfl

end GlobalTheory.ThK.Dbl

end
end
