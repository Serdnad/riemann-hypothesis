module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle178
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem chainTie_and_v0Onto :
    ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool)
      (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), (R.DcPt → M.ChainTie) ∧ (R.ReadingFormsSpanGoodSubspace → M.GoodPartHasComplexCoordinates) := by
  intro D Bs A X fc s R cr M
  refine ⟨fun h u x y => ?_, fun h => ?_⟩
  · rw [M.cφ_eq, M.cF_eq]
    exact (h u x y).symm
  · unfold Seam.GoodPartHasComplexCoordinates
    rw [← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, M.cF_eq y⟩

end GlobalTheory.Mem.SJ
end

section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dite_eq_left h]
  exact σ.injective h.choose_spec

theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dite_eq_left h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem sharp_iota_eq (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [PrimeDegreeVariant.sharp_downTo]
  rfl

theorem exists_read_of_matrix_tie (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (hv : Bs.v0 = InfinitePlace.mk D.what₂.embLL) {n : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ)
    (H E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin ((fc X.zs).Df1.nV Bs.μ0)) D.what₂.LL)
    (wU : D.what₂.Word → (fc X.zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin (X.data cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (hF : FormsTie D.what₂.embLL (W := (RowSide.sharp D).Amb μ) jA H E ((RowSide.sharp D).eOp μ))
    (hE : LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin)
    (hι : ∀ y, (RowSide.sharp D).iota μ (jA (V.mulVec y)) =
      (RowSide.sharp D).jEE (eRR (((X.data cr true).ι Bs.μ0).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec y))))
    (hNu : ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (wU u)) (eNu u)) :
    ∃ Rd : Read D X fc (twAt D.what₂.embLL Bs.v0), HEq Rd.wU wU ∧ HEq Rd.eNu eNu ∧ HEq Rd.eRR eRR ∧
      (∀ y, HEq (Rd.jV y) (jA (V.mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd cr ∧ Rd.NuTie ∧
      ((∃ L, HLatTie D.div.RR L (X.data cr true).XE eRR) → Rd.RRTie cr) ∧
      ((∀ (u : D.what₂.Word) (x : Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL)
          (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
          D.what₂.embLL ((fc X.zs).Dc.Pt (wU u) Bs.μ0 x y) =
            D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec y))) → Rd.DcPt) := by
  subst hμ
  refine ⟨⟨wU, eNu, eRR, jA.comp V.mulVecLin, hv, fun a => ?_⟩, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl,
    ?_, fun y => ?_, hNu, fun h => h, fun h => h⟩
  · rw [emb_eq D.what₂.embLL Bs.v0 a, sgAt_mk D.what₂.embLL hv]
  · exact (GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (W := (RowSide.sharp D).Amb D.what₂.mu0) jA H E _ V hF hE).symm
  · have h := hι y
    rw [sharp_iota_eq] at h
    exact h

end GlobalTheory.Mem.SJ
end

section

noncomputable section

namespace GlobalTheory.Mem.SJ.RowB

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iC_cpt_eq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, cpt, RingHom.id_apply]

theorem theta_eq : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y))) := by
  intro D Bs A X fc s R cr M eV hF hI y
  rw [M.cF_eq, hI y, M.eR_eq, X.rowMat_base cr true hF.h2, Matrix.one_mulVec, iC_cpt_eq, hF.theta y]
  rfl

end GlobalTheory.Mem.SJ.RowB

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.ChiLaws

theorem infDiag_mul_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    _root_.Formalism.L2.Host.infDiag k * finPartI L (_root_.Neutral.B1.diagUnits L k) = _root_.Neutral.B1.diagUnits L k := by
  have h : ((_root_.Formalism.L2.Host.infDiag k : _root_.Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold _root_.Formalism.L2.Host.infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
      ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem phase_sq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem chi_laws (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : _root_.Formalism.L2.Host.HChar H.E) (hχ : _root_.Formalism.L2.Host.IsChiPsi H χ) :
    (∀ x ∈ UOT H, tildeD H χ x = 1) ∧
    (letI := H.cmStar; ∀ z : unitary H.E,
      ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_UOT H).1 hx
    rw [tildeD_mk H hK]
    refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_
    refine hχ.unr v y ?_
    unfold _root_.Formalism.L2.Host.IsUnitAt
    rw [hy]
    exact ha v
  · letI := H.cmStar
    intro z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H
    obtain ⟨k, hk⟩ := h2 z
    rw [← h1 k z hk, tildeD_mk H hK]
    have e := congrArg χ.1 (infDiag_mul_finPart k)
    rw [map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv] at e
    have hi : ((χ.1 (_root_.Formalism.L2.Host.infDiag k) : ℂˣ) : ℂ) = _ := hχ.inf k
    rw [e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine phase_sq ((map_ne_zero _).2 k.ne_zero) ?_
    have hc : _root_.Formalism.L2.Host.embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (_root_.Formalism.L2.Host.embPsi H τ (k : H.E)) :=
      H.conjE_apply _ _
    rw [← hc]
    exact (map_mul (_root_.Formalism.L2.Host.embPsi H τ) _ _).symm.trans (congrArg _ hk)

end GlobalTheory.Mem.ChiLaws
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.ModelChar

def argU : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem argU_val (z : ℂˣ) : ((argU z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_argU (z : ℂˣ) : ‖((argU z : ℂˣ) : ℂ)‖ = 1 := by
  rw [argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_argU : Continuous argU := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero

variable {L : Type} [Field L] [NumberField L]

def finEv (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEv (w : InfinitePlace L) : AdeleRing (𝓞 L) L →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_finEv (v : HeightOneSpectrum (𝓞 L)) : Continuous (finEv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_infEv (w : InfinitePlace L) : Continuous (infEv w) :=
  (continuous_apply w).comp continuous_fst

theorem finEv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv v) (_root_.Neutral.B1.localIdele L v x) = x := by
  classical
  apply Units.ext
  exact Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem finEv_local_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv w) (_root_.Neutral.B1.localIdele L v x) = 1 := by
  classical
  apply Units.ext
  exact Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem infEv_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (infEv w) (_root_.Neutral.B1.localIdele L v x) = 1 := Units.ext rfl

theorem finEv_inf (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (finEv v) (_root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = 1 := Units.ext rfl

theorem infEv_inf_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (infEv w) (_root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)

theorem infEv_inf_ne {w u : InfinitePlace L} (h : u ≠ w) (x : (w.Completion)ˣ) :
    Units.map (infEv u) (_root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)

theorem infEv_infDiag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (_root_.Formalism.L2.Host.infDiag k) = _root_.Formalism.L2.Host.atInf w k := by
  unfold _root_.Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact infEv_inf_self w _
  · intro u _ hu
    exact infEv_inf_ne hu.symm _
  · simp

theorem finEv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (_root_.Formalism.L2.Host.infDiag k) = 1 := by
  unfold _root_.Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => finEv_inf v w _

theorem infEv_diag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (_root_.Neutral.B1.diagUnits L k) = _root_.Formalism.L2.Host.atInf w k := Units.ext rfl

theorem finEv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (_root_.Neutral.B1.diagUnits L k) = _root_.Formalism.L2.Host.atFin v k :=
  Units.ext rfl

theorem continuous_of_tameLoc {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ} (h : TameLoc v θ) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion L) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ) :=
    (ho.preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h.2 x ?_ ?_).symm
  · have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
    rwa [add_sub_cancel] at this
  · have := (WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1
    apply this
    rw [← WithZero.exp_add]
    simpa using hx


open Classical in
theorem exists_modelChar : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (n : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ), (∀ v ∈ S, TameLoc v (θ v)) → ∃ ψ : _root_.Neutral.B1.Ideles L →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ i (k : Lˣ), ((ψ (_root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L (InfinitePlace.mk (φ i)) (_root_.Formalism.L2.Host.atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧ (∀ v ∈ S, ∀ x, ψ (_root_.Neutral.B1.localIdele L v x) = θ v x) ∧ (∀ v ∉ S, ∀ x, ψ (_root_.Neutral.B1.localIdele L v x) = 1) ∧ ∀ k : Lˣ, ψ (_root_.Neutral.B1.diagUnits L k) = ψ (_root_.Formalism.L2.Host.infDiag k) * ∏ v ∈ S, θ v (_root_.Formalism.L2.Host.atFin v k) := by
  intro L _ _ I _ φ hφ n S θ hθ
  choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : _root_.Neutral.B1.Ideles L →* ℂˣ, ∀ a, ψ a =
      (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
        ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨{ toFun := fun a =>
        (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
          ∏ v ∈ S, θ v (Units.map (finEv v) a)
       map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one]
       map_mul' := fun a b => by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm] }, fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (ψ : _root_.Neutral.B1.Ideles L → ℂˣ) = _ from funext hψ]
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)
    · exact (continuous_argU.comp ((Continuous.units_map _ (hec i)).comp
        (Continuous.units_map _ (continuous_infEv _)))).zpow _
    · exact (continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))
  · intro x
    rw [hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod,
      Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · exact fun v hv => (hθ v hv).1 _
    · intro i _
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]
  · intro i k
    rw [hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self,
      Units.val_zpow_eq_zpow_val, argU_val, ← he i k]
    · rfl
    · intro j _ hj
      rw [infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]
    · simp
    · intro v _
      rw [finEv_inf, map_one]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    · intro w _ hw
      rw [finEv_local_ne hw, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]
    · intro w hw
      have hne : w ≠ v := fun hh => hv (hh ▸ hw)
      rw [finEv_local_ne hne, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro k
    rw [hψ, hψ]
    simp only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]

end GlobalTheory.ModelChar
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.relativeLatticeDeterminantClass_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  first | exact @GlobalTheory.Mem.Chr.relDetT_laws | exact GlobalTheory.Mem.Chr.relDetT_laws | (intros; apply GlobalTheory.Mem.Chr.relDetT_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hasDerivAt_inner_polynomial_moving_gaussian : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  first | exact @GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | exact GlobalTheory.OscPairDer.hasDerivAt_inner_gauss | (intros; apply GlobalTheory.OscPairDer.hasDerivAt_inner_gauss <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  first | exact @GlobalTheory.twistConeVanishing_of_cut | exact GlobalTheory.twistConeVanishing_of_cut | (intros; apply GlobalTheory.twistConeVanishing_of_cut <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory
open Classical


theorem _root_.GlobalTheory.T.inertPath_card_comm_latticePaths : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}, (∀ R : ST, R.1 ≠ P) → (∀ w : SG, w.1 ≠ P) →
  ∀ (s t : List ℕ) (d f : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)),
    Nonempty ({Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal s d.1.N Y ∧ IsInertNbr P.asIdeal t Y f.1.N} ≃
      {Y : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E Y ∧ IsUnimodular (hStd E n) Y ∧
        IsInertNbr P.asIdeal t d.1.N Y ∧ IsInertNbr P.asIdeal s Y f.1.N}) →
    ((d.inertNb P.asIdeal s).filter fun e => f ∈ e.inertNb P.asIdeal t).card =
      ((d.inertNb P.asIdeal t).filter fun e => f ∈ e.inertNb P.asIdeal s).card := by
  first | exact @GlobalTheory.inertPath_card_comm | exact GlobalTheory.inertPath_card_comm | (intros; apply GlobalTheory.inertPath_card_comm <;> assumption)
end
