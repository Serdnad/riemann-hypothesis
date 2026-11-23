module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431

@[expose] public section

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

theorem mat_eq_of_isIdTorusElt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha
  obtain ⟨h1, h2, h3⟩ := ha
  have hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
    rw [← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  set A := (matHom _ σ J a).1 with hAdef
  set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs
  set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs
  set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP
  have hXP : Xs * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hYP : Ys * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hAP : A * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Xs *ᵥ fun k => P k j) k = 0
        rw [show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]; rfl
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Ys *ᵥ fun k => P k j) k = 0
        rw [show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]; rfl
    have := congrFun (h3 _ hz) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hsum : P + adMat F X * Ys + adMat F Y * Xs = 1 := by rw [hP]; abel
  have hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs := by
    calc A = A * (P + adMat F X * Ys + adMat F Y * Xs) := by rw [hsum, Matrix.mul_one]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]
  have hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1 := fun f => by
    rw [← diagonal_one, diagonal_sub]
  rw [hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]
  abel

end GlobalTheory.IdTorus
end

section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem idelicFrameTorusElement_apply_column_decomposition {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y l a) (z : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J a).1 *ᵥ z =
      adMat F X *ᵥ (diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)) +
      adMat F Y *ᵥ (diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) +
      (z - adMat F X *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)
         - adMat F Y *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) := by
  set P := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)
  set Q := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      adMat F A * adMat F B = adMat F (A * B) := fun A B => (Matrix.map_mul).symm
  have hPX : P * adMat F X = 0 := by rw [mm, hW.xx]; simp
  have hPY : P * adMat F Y = 1 := by rw [mm, hW.xy]; simp
  have hQX : Q * adMat F X = 1 := by rw [mm, yx h hJ hW]; simp
  have hQY : Q * adMat F Y = 0 := by rw [mm, hW.yy]; simp
  set w := z - adMat F X *ᵥ (Q *ᵥ z) - adMat F Y *ᵥ (P *ᵥ z) with hw
  have hPw : P *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := P) (N := adMat F X), mulVec_mulVec (M := P) (N := adMat F Y), hPX, hPY,
      zero_mulVec, one_mulVec]; simp
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := Q) (N := adMat F X), mulVec_mulVec (M := Q) (N := adMat F Y), hQX, hQY,
      zero_mulVec, one_mulVec]; simp
  have hmem : w ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
    refine ⟨(Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_,
      (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_⟩
    · exact congrFun hPw i
    · exact congrFun hQw i
  have hz : z = adMat F X *ᵥ (Q *ᵥ z) + adMat F Y *ᵥ (P *ᵥ z) + w := by rw [hw]; abel
  conv_lhs => rw [hz]
  rw [mulVec_add, mulVec_add, mulVec_mulVec (N := adMat F X), mulVec_mulVec (N := adMat F Y), ha.1, ha.2.1,
    ha.2.2 w hmem, ← mulVec_mulVec, ← mulVec_mulVec]

theorem isIdTorusElt_uniq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l b → a = b := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a b ha hb
  apply matHom_injective (AF F) σ J
  apply Units.ext
  have hv : ∀ z, (matHom _ σ J a).1 *ᵥ z = (matHom _ σ J b).1 *ᵥ z := fun z => by
    rw [idelicFrameTorusElement_apply_column_decomposition h hJ hW ha, idelicFrameTorusElement_apply_column_decomposition h hJ hW hb]
  ext i j
  simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i

end GlobalTheory.IdTorus

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_one_nonneg {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (v : VV ℂ lam) :
    0 ≤ nrm lam (fun _ => 1) v := by
  by_cases hv : v = 0
  · simp [nrm, hv]
  · exact (Complex.le_def.1 (GlobalTheory.CoefModel.pairK_pos lam (fun _ => Matrix.PosDef.one) v hv).le).1

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatRowAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)), ∀ u,
    ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjRowAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m))),
    (∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ),
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.RatTop

theorem exists_linearMap_of_repr_mem_range {K : Type} [Field K] (φ : K →+* ℂ) {VS VT WS WT : Type}
    [AddCommGroup VS] [Module K VS] [AddCommGroup VT] [Module K VT]
    [AddCommGroup WS] [Module ℂ WS] [AddCommGroup WT] [Module ℂ WT]
    (mS : VS →ₛₗ[φ] WS) (mT : VT →ₛₗ[φ] WT) {ι κ : Type} [Fintype ι] [Fintype κ]
    (b0 : Module.Basis ι K VS) (bS : Module.Basis ι ℂ WS) (bT : Module.Basis κ ℂ WT)
    (uS : ι → VS) (uT : κ → VT) (hS : ∀ i, mS (uS i) = bS i) (hT : ∀ k, mT (uT k) = bT k)
    (L : WS →ₗ[ℂ] WT) (hL : ∀ k i, bT.repr (L (bS i)) k ∈ Set.range φ) :
    ∃ f : VS →ₗ[K] VT, ∀ u, L (mS u) = mT (f u) := by
  classical
  haveI : FiniteDimensional K VS := Module.Finite.of_basis b0
  have hli : LinearIndependent K uS := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ i, φ (g i) • bS i = 0 := by
      have := congrArg mS hg

      simpa [map_sum, LinearMap.map_smulₛₗ, hS] using this
    have h2 := Fintype.linearIndependent_iff.mp bS.linearIndependent _ h1 i
    exact φ.injective (by rw [h2, map_zero])
  have hsp : Submodule.span K (Set.range uS) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis b0).symm
  let bS' : Module.Basis ι K VS := Module.Basis.mk hli hsp.ge
  choose m hm using hL
  let f : VS →ₗ[K] VT := bS'.constr K fun i => ∑ k, m k i • uT k
  refine ⟨f, fun u => ?_⟩
  have e : (L.comp mS : VS →ₛₗ[φ] WT) = (mT.comp f : VS →ₛₗ[φ] WT) := by
    refine bS'.ext fun i => ?_

    rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.mk_apply, hS, map_sum]
    conv_lhs => rw [← bT.sum_repr (L (bS i))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, hT, hm]
  exact LinearMap.congr_fun e u

end GlobalTheory.RatTop

namespace GlobalTheory.KerConjMean

theorem ratTopAt_big : BigC fun _ ch _ _ => RatTopAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c j
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).1 j
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun i => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro i
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ i).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k i
    have h := hr k i
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SumCount.DataCount

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [FiniteDimensional K V]

theorem finrank_le_dim (M : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
  have h1 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) V := Submodule.rank_le M
  have h2 : Module.rank (𝓞 K) V = Module.rank K V := (IsFractionRing.rank_right_eq (𝓞 K) K V).symm
  rw [h2, ← Module.finrank_eq_rank K V] at h1
  exact Module.finrank_le_of_rank_le h1

theorem card_quot_le_of_fg (M : Submodule (𝓞 K) V) [Module.Finite (𝓞 K) M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ∧
      Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h1 : (a : K) • (x : V) = 0 := by
      have h0 : a • (x : V) = 0 := congrArg Subtype.val hx
      rwa [← algebraMap_smul K a] at h0
    have h2 : (a : K) ≠ 0 := by
      have := nonZeroDivisors.ne_zero ha
      exact_mod_cast this
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h2)
  have e := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (N := M) I
  have hN : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hI)
  rw [hN] at e
  refine ⟨Nat.finite_of_card_ne_zero (by rw [e]; exact (pow_pos hpos _).ne'), ?_⟩
  rw [e]
  exact Nat.pow_le_pow_right hpos (finrank_le_dim M)

theorem card_quot_le (M : Submodule (𝓞 K) V) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  by_cases hf : Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M))
  swap
  · haveI := not_finite_iff_infinite.1 hf
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  choose s hs using Submodule.Quotient.mk_surjective (I • ⊤ : Submodule (𝓞 K) M)
  let M' : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun q => (s q : V))
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact (s q).2)
  haveI : Module.Finite (𝓞 K) M' := Module.Finite.span_of_finite _ (Set.finite_range _)
  obtain ⟨hfin, hc⟩ := card_quot_le_of_fg M' hI
  let φ : (M' ⧸ (I • ⊤ : Submodule (𝓞 K) M')) →ₗ[𝓞 K] (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)
  have hφ : Function.Surjective φ := fun q =>
    ⟨Submodule.Quotient.mk ⟨s q, Submodule.subset_span ⟨q, rfl⟩⟩, hs q⟩
  exact (Nat.card_le_card_of_surjective φ hφ).trans hc

end General

theorem absNorm_le_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm w.asIdeal ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ 2 := by
  have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) (w.under (𝓞 F)).asIdeal
  rw [hr] at h1
  rw [← h1]
  refine Nat.le_of_dvd ?_ (Ideal.absNorm_dvd_absNorm_of_le Ideal.map_comap_le)
  rw [h1]
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot)) _

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sig_nonneg : 0 ≤ sig G :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem absNorm_modul_le : (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  unfold sig
  rw [Finset.mul_sum, Real.exp_sum]
  show ((Ideal.absNorm (∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v) : ℕ) : ℝ) ≤ _
  rw [map_prod, Nat.cast_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun v hv => ?_
  have h1 := absNorm_le_sq D.sp.cm.deg2 (G.pl.w v)
  rw [G.pl.under_w hv] at h1
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have e : Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
    rw [← pow_mul, ← mul_assoc, ← Nat.cast_ofNat, ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpos]
  rw [e, map_pow, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h1) _

theorem rank_row_le {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i 0)).rank ≤ bigN D := by
  have hr : (G.V (.grid i 0)).rank = rankV D i 0 := by
    cases i with
    | zero =>
      refine (D.sp.Y_rank _ (min_le_right _ _)).trans ?_
      rw [min_eq_left (Nat.zero_le _)]
      simp [rankV, Ranks.rankY]
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).rank
  have h1 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have hk : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr]
  simp only [rankV, bigN]
  have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  rw [e]
  omega

theorem card_cosAt_le {i : ℕ} (hi : i < D.R.m) :
    (Nat.card (G.CosAt i) : ℝ) ≤ Real.exp ((bigN D : ℝ) ^ 2 * (2 * sig G)) := by
  have h1 := card_quot_le (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) (G.pl.modul_ne_bot sc)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, Fintype.card_fin] at h1
  have hpos : 0 < Ideal.absNorm G.modul := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (G.pl.modul_ne_bot sc))
  have h2 : (G.V (.grid i 0)).rank * (G.V (.grid (i + 1) 0)).rank ≤ bigN D ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (rank_row_le G hi.le) (rank_row_le G hi)
  have h3 : Nat.card (G.CosAt i) ≤ Ideal.absNorm G.modul ^ (bigN D ^ 2) := h1.trans (Nat.pow_le_pow_right hpos h2)
  calc (Nat.card (G.CosAt i) : ℝ) ≤ (Ideal.absNorm G.modul : ℝ) ^ (bigN D ^ 2) := by exact_mod_cast h3
    _ ≤ Real.exp (2 * sig G) ^ (bigN D ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_modul_le G) _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem card_datum_le : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * ((bigN D : ℝ) ^ 2 * (2 * sig G))) := by
  rw [Nat.card_pi, Nat.cast_prod, Real.exp_nat_mul]
  refine (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ => card_cosAt_le G i.2).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_datum_le_aOne {C b : ℝ} (hC : 2 ≤ C) (hb : 1 ≤ b) : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne G C b) := by
  refine (card_datum_le G).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hl := Real.log_nonneg hb
  have hs : 0 ≤ (bigN D : ℝ) ^ 2 * sig G := mul_nonneg (by positivity) (sig_nonneg G)
  have h1 : 0 ≤ C * D.R.f * bigN D * b * Real.log b := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ b := by linarith
    positivity
  have h2 : 2 ≤ C * D.R.m := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hs
  unfold aOne
  nlinarith

theorem dataK : GlobalTheory.SumCount.DataK := by
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  exact card_datum_le_aOne ch.G hC (Real.one_le_exp (by linarith))

end GlobalTheory.SumCount.DataCount

end
end

section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_smul {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type}
    (_hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (hΛ : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := by

  have key : ∀ a : k', valuation k' a ≤ 1 → ∀ y ∈ Λ₂, a • y ∈ Λ₂ := fun a ha y hy =>
    Λ₂.smul_mem (⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩ : 𝒪[k']) hy
  have hc₂ : valuation k' (c₂ : k') ≠ 0 := by simp
  set u : k' := (c₂⁻¹ : k'ˣ) * j c with hu
  have hu1 : valuation k' u = 1 := by
    rw [hu, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_mul_cancel₀ hc₂]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hu1' : valuation k' u⁻¹ = 1 := by rw [map_inv₀, hu1, inv_one]
  intro x
  rw [mem_smul_lat, mem_smul_lat, ← hΛ]
  have heq : (c₂⁻¹ : k'ˣ) • (fun d => j (x (cD d))) = u • (fun d => j (((c⁻¹ : kˣ) • x) (cD d))) := by
    funext d
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, hu, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  rw [heq]
  constructor
  · intro h
    have := key u⁻¹ hu1'.le _ h
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this
  · exact key u hu1.le _

end GlobalTheory.PureMatch.Transport
end
end
