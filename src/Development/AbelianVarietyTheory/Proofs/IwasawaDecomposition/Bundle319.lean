module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
public import Formalism.LocalToGlobal.Columns.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle303
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalUnitaryPairToPairComponentMemLocalLevel
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.RowsSign

open MvPolynomial
open scoped ComplexOrder

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem degree_of_colWeight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul_of_weight {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

def totDeg (lam : ι → DomWeight n) : ℕ := ∑ τ, ∑ j, (lam τ).natW j

theorem blockAct_smul_of_mem (lam : ι → DomWeight n) (a : K) (M : ι → Matrix (Fin n) (Fin n) K)
    {y : Formalism.L2.DIV.Pol K ι n} (hy : y ∈ Formalism.L2.DIV.VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => a • M τ) y = a ^ totDeg lam • Formalism.GradedWeylDivisibility.blockAct K M y := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have hT := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => a • M τ)).1
    have hT' := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (a • M τ) (F τ)) =
        C (a ^ (∑ j, (lam τ).natW j)) * Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (M τ) (F τ)) := by
      intro τ
      rw [rowAct_smul_of_weight a (M τ) (F τ) (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.1 (hF τ)).1, map_smul, smul_eq_C_mul]
    rw [map_prod, map_prod]
    simp only [hT, hT']
    rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      smul_eq_C_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

variable [StarRing K]

def negSign (lam : ι → DomWeight n) : K := gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * (-1) ^ totDeg lam

theorem pairK_neg (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (x y : Formalism.L2.DIV.VV K lam) :
    pairK lam (fun τ => -G τ) x y = negSign lam * pairK lam G x y := by
  have hy := blockAct_smul_of_mem lam (-1 : K) (fun τ => (G τ)ᵀ) y.2
  have hT : (fun τ => (-G τ)ᵀ) = fun τ => (-1 : K) • (G τ)ᵀ := by
    funext τ
    rw [Matrix.transpose_neg, neg_one_smul]
  have hg : gramTw lam (fun τ => -G τ) = gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam G := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← mul_zpow, ← Matrix.det_mul, neg_mul, one_mul]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul]
  rw [hT, hy, map_smul, hg, negSign, smul_eq_mul]
  ring

theorem negSign_mul_self (lam : ι → DomWeight n) : negSign (K := K) lam * negSign lam = 1 := by
  have hd : ((-1 : Matrix (Fin n) (Fin n) K)).det * ((-1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [← Matrix.det_mul, neg_mul_neg, one_mul, Matrix.det_one]
  have hz : ∀ e : ℤ, ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e * ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e = 1 := by
    intro e
    rw [← mul_zpow, hd, _root_.one_zpow]
  have hp : ((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => hz _
  calc negSign (K := K) lam * negSign lam
      = (gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K))) *
        (((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam) := by unfold negSign; ring
    _ = 1 := by rw [hgg, hp, one_mul]

end General

end GlobalTheory.RowsSign

namespace GlobalTheory.RowsSign

open scoped ComplexOrder InnerProductSpace

theorem pairV_neg_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (φ : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (c0 : Formalism.L2.DIV.VV K lam →ₛₗ[φ] W)
    (h : ∀ x y, inner ℂ (c0 x) (c0 y) = φ (pairV emb lam (-1) x y)) :
    ∀ x y, pairV emb lam (-1) x y = pairV emb lam 1 x y := by
  have hG : gramK emb (-1 : Matrix (Fin n) (Fin n) E) = fun τ => -(gramK emb 1 τ) := by
    funext τ
    ext i j
    simp [gramK, Matrix.neg_apply, Matrix.one_apply]
  have hneg : ∀ x y, pairV emb lam (-1) x y = negSign lam * pairV emb lam 1 x y := by
    intro x y
    unfold pairV
    rw [hG, pairK_neg]
  by_cases hnt : Nontrivial (Formalism.L2.DIV.VV K lam)
  · rcases mul_self_eq_one_iff.1 (negSign_mul_self (K := K) lam) with hc | hc
    · intro x y
      rw [hneg, hc, one_mul]
    · exfalso
      have hpos := Formalism.L2.DIV.pairPos K ι n lam (gramK emb 1) φ (fun τ => by
        have : ((gramK emb (1 : Matrix (Fin n) (Fin n) E) τ).map φ) = 1 := by
          ext i j
          simp [gramK, Matrix.one_apply]
        rw [this]
        exact Matrix.PosDef.one)
      obtain ⟨i⟩ := (bVV K lam).index_nonempty
      have h1 := hpos.diag_pos (i := i)
      simp only [Matrix.of_apply] at h1
      have h2 := h (bVV K lam i) (bVV K lam i)
      rw [hneg, hc, neg_one_mul, map_neg] at h2
      have h3 := inner_self_nonneg (𝕜 := ℂ) (x := c0 (bVV K lam i))
      rw [h2, map_neg, RCLike.re_to_complex] at h3
      have h4 := (Complex.lt_def.1 h1).1
      have h5 : (φ (pairV emb lam 1 (bVV K lam i) (bVV K lam i))).re =
          (φ (pairK lam (gramK emb 1) (bVV K lam i) (bVV K lam i))).re := rfl
      simp only [Complex.zero_re] at h4
      linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    intro x y
    rw [Subsingleton.elim x 0]
    simp

end GlobalTheory.RowsSign

open GlobalTheory.RowsSign in
theorem GlobalTheory.RowsSign.pairV_gramR_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (c0R : Formalism.L2.DIV.VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W), cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) → Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) → (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) → ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR x y = pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) X.toD7.sp.X'.gram x y := by
  intro X px I hI cX gramR c0R hcX hg htie hinner x y
  have hJ : X.toD7.sp.X'.gram = 1 := by
    obtain ⟨hs, -, h2, -⟩ := hI.spaces
    change X.B.sp.X'.gram = 1
    rw [h2]
    refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
    simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]
  rcases hg with rfl | rfl
  · rfl
  · rw [hJ] at hinner ⊢
    exact pairV_neg_one_eq _ _ _ c0R hinner x y
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LevFinCong

variable {D : D7}

theorem finE_mem_UA (V : HSp D) (κ : GA D V) : finE V κ ∈ UA D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have := (GlobalTheory.Mass.swapPts (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem isOpen_comap_Kg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    IsOpen ((((Kg D.sp.cm V.gram β T).comap
      ((Formalism.UG.bc (swapAE D)).comp (Bridge.Gf V).subtype)) : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hc : Continuous ((Bridge.Gf V).subtype) := continuous_subtype_val
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β T hc (map_one _)] with x hh
  obtain ⟨h2, h3⟩ := hh
  obtain ⟨g, hg⟩ := x.2
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ UA D.sp.cm V.gram := by
    rw [← hg]; exact finE_mem_UA V g
  exact ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

theorem exists_finCong_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ levS V β L ∧ levChi V β L k = 1 := by
  classical
  intro D V β L
  obtain ⟨N, hN, hK⟩ := GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (isOpen_comap_Kg V β (L.Pg ∪ L.Q))
  refine ⟨N, hN, fun k hf hk => ?_⟩
  have hk' : finE V k ∈ Kg D.sp.cm V.gram β (L.Pg ∪ L.Q) := hK k hk
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right hk'
  · unfold levChi
    rw [GlobalTheory.GoodFiniteDim.levFn_eq_one Finset.subset_union_left Finset.subset_union_right hk', Units.val_one]

end GlobalTheory.LevFinCong
end
end

section

noncomputable section

namespace GlobalTheory.Mem.TypePl

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp NumberField IsDedekindDomain
open scoped Pointwise

section Places

variable {R : Ranks} {H : Host R}

theorem isConjPl_iff_conjPl (w w' : PlE H) : IsConjPl H w w' ↔ Chr.ConjPl H.conj.toRingEquiv w w' :=
  (HalfPlaces.isConjPl_iff H w w').trans (Chr.conjPl_iff_smul H.conj w w').symm

theorem under_eq_iff (w w' : PlE H) : w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ w' = w ∨ IsConjPl H w w' := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [Chr.under_eq_iff_conjPl c hcm.rank hcm.ne, isConjPl_iff_conjPl]
  have e : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  rw [e]

theorem under_mem {p : ℕ} {w : PlE H} : w.under (𝓞 H.F) ∈ placesOver H.F p ↔ w ∈ placesOver H.E p := by
  show algebraMap (𝓞 H.F) (𝓞 H.E) ((p : ℕ) : 𝓞 H.F) ∈ w.asIdeal ↔ _
  rw [map_natCast]
  rfl

theorem exists_under (v : HeightOneSpectrum (𝓞 H.F)) : ∃ w : PlE H, w.under (𝓞 H.F) = v := by
  have := v.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 H.E)))
  exact ⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩, HeightOneSpectrum.ext hWv.over.symm⟩

theorem div_over (P : PiBar H) {k : Fin 2} {w : PlE H} (h : P.Div k w) : w ∈ placesOver H.E (H.g k) := by
  have h1 := P.pb_over k
  rw [← (show w.under (𝓞 H.K) = P.pb k from h)] at h1
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at h2

theorem div_iff_not_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : w ∈ placesOver H.E (H.g k)) (h : IsConjPl H w w') : P.Div k w ↔ ¬ P.Div k w' :=
  ((Chr.splitsC_main R H (H.g k) (H.g_prime k) hs w hw).2.2.2 (P.pb k) (P.pb_over k) w'
    ((isConjPl_iff_conjPl w w').1 h)).2

theorem not_isConjPl (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : P.Div k w) (hw' : P.Div k w') : ¬ IsConjPl H w w' :=
  fun h => (div_iff_not_div P hs (div_over P hw) h).1 hw hw'

def below {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p) (i : I) : placesOver H.F p :=
  ⟨(pl i).under (𝓞 H.F), under_mem.2 (h i)⟩

theorem below_injective {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Injective (below pl h) :=
  fun i j e => ((under_eq_iff (pl j) (pl i)).1 (congrArg Subtype.val e)).elim (fun e => h1 e) fun e => absurd e (h2 j i)

theorem card_placesOver {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    Nat.card (placesOver H.F p) = R.f := by
  obtain ⟨e, h, h1, h2, h3⟩ := HalfPlaces.exists_places_cover H hp hs
  have hb : Function.Bijective (below e h) := by
    refine ⟨below_injective e h h1 h2, fun v => ?_⟩
    obtain ⟨w, hw⟩ := exists_under v.1
    obtain ⟨i, hi⟩ := h3 w (under_mem.1 (hw ▸ v.2))
    exact ⟨i, Subtype.ext (((under_eq_iff (e i) w).2 hi).symm.trans hw)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem below_bijective {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E)
    {I : Type} [Fintype I] (hI : Fintype.card I = R.f) (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Bijective (below pl h) := by
  have hc := card_placesOver hp hs
  haveI : Finite (placesOver H.F p) := Nat.finite_of_card_ne_zero (hc ▸ (GaloisStage.f_pos R).ne')
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨below_injective pl h h1 h2, by rw [hc, Nat.card_eq_fintype_card, hI]⟩

theorem existsUnique_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : ∃! w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
  obtain ⟨w, hw⟩ := exists_under v.1
  have hex : ∃ w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
    by_cases h : P.Div k w
    · exact ⟨w, h, hw⟩
    · obtain ⟨w', hw', -⟩ := Chr.existsUnique_conjPl H.conj.toRingEquiv w
      have hc := (isConjPl_iff_conjPl w w').2 hw'
      refine ⟨w', ?_, ((under_eq_iff w w').2 (Or.inr hc)).trans hw⟩
      by_contra h'
      exact h ((div_iff_not_div P hs (under_mem.1 (hw ▸ v.2)) hc).2 h')
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun b hb => ?_⟩
  exact ((under_eq_iff a b).1 (hb.2.trans ha.2.symm)).elim id fun e => absurd e (not_isConjPl P hs ha.1 hb.1)

def above (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : PlE H := (existsUnique_div P hs v).choose

theorem above_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : P.Div k (above P hs v) := (existsUnique_div P hs v).choose_spec.1.1

theorem above_under (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : (above P hs v).under (𝓞 H.F) = v := (existsUnique_div P hs v).choose_spec.1.2

theorem above_injective (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    Function.Injective (above P hs) :=
  fun v v' e => Subtype.ext (by rw [← above_under P hs v, e, above_under])

end Places

section Labels

def labDat (g : ℕ) [Fact g.Prime] : LabelDatum g := (LabelModel.inhab g).some

variable {g : ℕ} [Fact g.Prime]

def charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : (ZMod g)ˣ :=
  Units.mk0 (GLp.Model.isCharLab_exists L ω).choose (GLp.Model.isCharLab_exists L ω).choose_spec.1

theorem isCharLab_charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : IsCharLab L ω (charLab L ω) :=
  (GLp.Model.isCharLab_exists L ω).choose_spec

theorem isCharLab_pow (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) (n : ℕ) :
    IsCharLab L (ω ^ n) ((charLab L ω ^ n : (ZMod g)ˣ) : ZMod g) := by
  refine ⟨Units.ne_zero _, fun u hu => ?_⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow,
    (isCharLab_charLab L ω).2 u hu]

theorem orderOf_charLab (L : LabelDatum g) {ω : (ZMod g)ˣ →* ℂˣ} (h : Function.Injective ω) :
    orderOf (charLab L ω) = g - 1 := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have e : T (charLab L ω) = (ω u : ℂ) := ((isCharLab_charLab L ω).2 u hu).symm
  rw [← orderOf_injective T hT, e, orderOf_units, orderOf_injective ω h, ho]

theorem thetaOf_of_isCharLab (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (a : (ZMod g)ˣ) : thetaOf L 1 (algebraMap (ZMod g) _ c) (algebraMap (ZMod g) _ (a : ZMod g)) = ((χ a : ℂˣ) : ℂ) := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u ^ m = a := mem_powers_iff_mem_zpowers.2 (htop ▸ Subgroup.mem_top a)
  have hcp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc.1, map_one]
  rw [Units.val_pow_eq_pow_val, map_pow, hu, LabelModel.thetaOf_pow g L one_pos hcp, map_pow,
    Units.val_pow_eq_pow_val, hc.2 u hu]

end Labels

end GlobalTheory.Mem.TypePl

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

theorem pairOf_act_of_agree {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M N : Submodule R V)
    (pr : M →+ W) (pr' : N →+ W') (hs : ∀ (a : R) z, pr (a • z) = res a • pr z)
    (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z) (φ : Module.Dual k W) (g : Module.Dual k W') (e : V ≃ₗ[R] V)
    (hL : loc res (M.map (e : V →ₗ[R] V)) = loc res N)
    (hf : ∀ (x : M) (hx : e x.1 ∈ N), φ (pr x) = g (pr' ⟨_, hx⟩)) :
    ((pairOf res M pr φ).act e).L = loc res N ∧
      ∀ x ∈ loc res N, ((pairOf res M pr φ).act e).f x = g (locExt res N pr' x) := by
  have hmem : ∀ x, e.symm x ∈ loc res M ↔ x ∈ loc res N := by
    intro x
    rw [← hL, mem_loc, mem_loc]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [Submodule.mem_map_equiv, map_smul]
  refine ⟨Submodule.ext fun x => (Pr.mem_act e _ x).trans (hmem x), fun x hx => ?_⟩
  have hx' := (hmem x).2 hx
  obtain ⟨s, hs0, h1⟩ := (mem_loc res M _).1 hx'
  obtain ⟨s', hs0', h2⟩ := (mem_loc res N _).1 hx
  have h1' : (s' * s) • e.symm x ∈ M := by rw [mul_smul]; exact M.smul_mem _ h1
  have h2' : (s' * s) • x ∈ N := by rw [mul_comm, mul_smul]; exact N.smul_mem _ h2
  have hne : res (s' * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hs0' hs0
  have he : e ((s' * s) • e.symm x) = (s' * s) • x := by rw [map_smul, e.apply_symm_apply]
  have h3 := hf ⟨_, h1'⟩ (by rw [he]; exact h2')
  have h4 : pr' ⟨e ((s' * s) • e.symm x), by rw [he]; exact h2'⟩ = pr' ⟨_, h2'⟩ := by
    congr 1; exact Subtype.ext he
  rw [h4, locExt_spec res M pr hs _ hx' _ h1', locExt_spec res N pr' hs' _ hx _ h2', map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at h3
  exact mul_left_cancel₀ hne h3

theorem pc_act_down : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (γ : GL (Fin (D.R.N i)) D.host.E), loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (clsCrd D u i hi c) → (∀ (x : ↥(Ld D u i hi c')) (hx : γ.1 *ᵥ x.1 ∈ Lk A i hi v c), (D.fm u).fv i v c' (P.pr v c' x) = g (P.prk v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).L = loc (A.res v) (Lk A i hi v c) ∧ ∀ x ∈ loc (A.res v) (Lk A i hi v c), ((pc P v c').act (glE γ)).f x = g (locExt (A.res v) (Lk A i hi v c) (P.prk v c) x) := by
  intro D u A i hi P K v c c' g γ hL hf
  refine pairOf_act_of_agree (A.res v) _ _ (P.pr v c') (P.prk v c) (P.pr_smul v c') (P.prk_smul v c) _ g (glE γ) ?_ hf
  rw [map_glE, hL, GlobalTheory.T.classLattice_sup_primeDual_localization_eq D u A i hi K v c]

end GlobalTheory.LevelHecke
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → (pc P v c').act (glE γ) = pc P v c → mov K (A.eV v).1 c γ c' ∈ K.lev.Uloc (A.eV v).1 := by
  first | exact @GlobalTheory.LevelHecke.PairToLevel.main | exact GlobalTheory.LevelHecke.PairToLevel.main | (intros; apply GlobalTheory.LevelHecke.PairToLevel.main <;> assumption)
end
