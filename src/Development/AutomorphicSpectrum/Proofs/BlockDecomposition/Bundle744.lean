module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle711
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle467

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem npow_mul' {r h : ℝ≥0} (t : ℂ) : npow (r * h) t = npow r t * npow h t := by
  simp only [npow, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg r.2 h.2 t

theorem npow_inv' {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r⁻¹ t = npow r (-t) := by
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  rw [npow_eq_exp hr', npow_eq_exp hr]
  congr 1
  rw [NNReal.coe_inv, Real.log_inv]
  push_cast
  ring

theorem npow_add' {r : ℝ≥0} (hr : 0 < r) (s t : ℂ) : npow r (s + t) = npow r s * npow r t := by
  rw [npow_eq_exp hr, npow_eq_exp hr, npow_eq_exp hr, ← Complex.exp_add]
  congr 1
  ring

theorem npow_zero' (r : ℝ≥0) (hr : 0 < r) : npow r 0 = 1 := by
  rw [npow_eq_exp hr]; simp

theorem upperLeft_blockMatrix {R : Type} (x y z t : Matrix (Fin n) (Fin n) R) : blkA (blk4 x y z t) = x := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem det_ad (a : GL (Fin n) (AE D)) :
    (Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) =
      conjUnit (R := AF D.host.F) D.sp.cm.sig (Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) := by
  apply Units.ext
  have h1 : ((Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) : AE D) = (adj (a⁻¹).1 : Mx D n n).det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  have h2 : (adj (a⁻¹).1 : Mx D n n).det = cA D ((a⁻¹).1.det) := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (cA D) _).symm
  have h3 : ((Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  rw [h1, h2, ← h3]
  rfl
theorem absA_ad (a : GL (Fin n) (AE D)) : absA D (Matrix.GeneralLinearGroup.det (ad a)) =
    (absA D (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rw [det_ad, GlobalTheory.DiagThetaRule.absA_conj, map_inv, map_inv]

theorem exists_ad (a : GL (Fin n) (AE D)) : ∃ m' ∈ P D n, mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
  obtain ⟨m', hm'⟩ := exists_levi (ad a)
  obtain ⟨m'', hm''⟩ := exists_levi (ad a)⁻¹
  have e1 : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
    rw [hm']
    have : (adj ((ad a)⁻¹).1 : Mx D n n) = a.1 := adj_adj _
    rw [this]
    rfl
  have h1 : m'' * m' = 1 := mat_inj (by
    rw [mat_mul, mat_one, hm', hm'']
    have := levi_mul_inv (D := D) (ad a)⁻¹
    rwa [inv_inv] at this)
  exact ⟨m', levi_mem_P hm' hm'' h1, e1⟩

theorem gram_pt (V : HSp D) (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    StdUnn.inner V (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n)
      (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n) = (gramQ V ξ).map (incA D) := by
  have h0 : gramQ V ξ = ξᴴ * (HSpace.gram V * ξ) := rfl
  have e : ((gramQ V ξ).map (incA D) : Mx D n n) =
      HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (gA V) (ξ.map (incA D)) : Mx D V.rank n) := by
    change rat (gramQ V ξ) = HMul.hMul (adj (rat ξ)) (HMul.hMul (gA V) (rat ξ) : Mx D V.rank n)
    rw [h0, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [e]
  unfold GlobalTheory.StdUnn.inner
  have u := GlobalTheory.MixModel.mt_unitary V h⁻¹
  calc _ = HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (HMul.hMul (adj (Formalism.L2.Theta.mt V h⁻¹))
        (HMul.hMul (gA V) (Formalism.L2.Theta.mt V h⁻¹) : Mx D V.rank V.rank) : Mx D V.rank V.rank) (ξ.map (incA D)) : Mx D V.rank n) := by
        rw [adj_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [u]

theorem ifrB_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (ν : Measure (GA D V)) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : Mx D n n} (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (β : HermE D n) :
    IfrB V ν (ω (m * u) φ).1 β = ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1))))) *
      IfrB V ν (fun x => φ.1 (HMul.hMul x a.1)) β := by
  set K : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1)))) with hK
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
      (ω (m * u) φ).1 (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      fun h => K * ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
        φ.1 (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)) : Mx D V.rank n) a.1) := by
    funext h
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [weil_pt hω a hm hu, inner_mul_right, gram_pt, x.2.2, hK]
    ring
  unfold IfrB
  rw [key]
  show ⨍ q, K * _ ∂_ = _
  simp only [average_eq, integral_const_mul, mul_smul_comm]
  rfl

end GlobalTheory.CompanionTheory.IwaAd
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.CgMod

section Abstract

variable {M : Type} [AddCommGroup M] [TopologicalSpace M]

def restr (S : AddSubgroup M) (U : M ≃ₜ+ M) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) : S ≃ₜ+ S where
  toFun s := ⟨U s.1, hU _ s.2⟩
  invFun s := ⟨U.symm s.1, hU' _ s.2⟩
  left_inv s := Subtype.ext (U.left_inv s.1)
  right_inv s := Subtype.ext (U.right_inv s.1)
  map_add' x y := Subtype.ext (map_add U x.1 y.1)
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

def dbl [IsTopologicalAddGroup M] (S : AddSubgroup M) (P : M →+ M) (hPc : Continuous P) (hPm : ∀ x, P x ∈ S)
    (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M) (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0)
    (h3 : ∀ x, P x + L (P (L.symm x)) = x) : (S × S) ≃ₜ+ M where
  toFun p := p.1.1 + L p.2.1
  invFun x := (⟨P x, hPm x⟩, ⟨P (L.symm x), hPm _⟩)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change P (p.1.1 + L p.2.1) = p.1.1
      rw [map_add (f := _), hPs _ p.1.2, h1 _ p.2.2, add_zero]
    · change P (L.symm (p.1.1 + L p.2.1)) = p.2.1
      have hl : L.symm (L p.2.1) = p.2.1 := L.left_inv _
      rw [map_add (f := _), map_add (f := _), h2 _ p.1.2, zero_add, hl, hPs _ p.2.2]
  right_inv x := h3 x
  map_add' p q := by
    change (p.1.1 + q.1.1) + L (p.2.1 + q.2.1) = (p.1.1 + L p.2.1) + (q.1.1 + L q.2.1)
    rw [map_add (f := _)]; abel
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_fst).add (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := (hPc.subtype_mk _).prodMk ((hPc.comp L.symm.continuous).subtype_mk _)

theorem char_sq [IsTopologicalAddGroup M] [LocallyCompactSpace M] [SecondCountableTopology M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (S : AddSubgroup M) [LocallyCompactSpace S] (P : M →+ M)
    (hPc : Continuous P) (hPm : ∀ x, P x ∈ S) (hPs : ∀ s ∈ S, P s = s) (L : M ≃ₜ+ M)
    (h1 : ∀ s ∈ S, P (L s) = 0) (h2 : ∀ s ∈ S, P (L.symm s) = 0) (h3 : ∀ x, P x + L (P (L.symm x)) = x)
    (U : M ≃ₜ+ M) (hUL : ∀ x, U (L x) = L (U x)) (hU : ∀ s ∈ S, U s ∈ S) (hU' : ∀ s ∈ S, U.symm s ∈ S) :
    addEquivAddHaarChar (restr S U hU hU') ^ 2 = addEquivAddHaarChar U := by
  haveI : SecondCountableTopology S := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space S := Topology.IsEmbedding.subtypeVal.t2Space
  set Ψ := dbl S P hPc hPm hPs L h1 h2 h3 with hΨ
  set T := restr S U hU hU' with hT
  have e : ((Ψ.symm.trans (GlobalTheory.ModuLR.prodCE T T)).trans Ψ) = U := by
    ext x
    obtain ⟨p, rfl⟩ := Ψ.surjective x
    change Ψ (GlobalTheory.ModuLR.prodCE T T (Ψ.symm (Ψ p))) = U (Ψ p)
    have hl : Ψ.symm (Ψ p) = p := Ψ.left_inv p
    rw [hl]
    change U p.1.1 + L (U p.2.1) = U (p.1.1 + L p.2.1)
    rw [map_add (f := _), hUL]
  rw [sq, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.ModuLR.addEquivAddHaarChar_transport Ψ (GlobalTheory.ModuLR.prodCE T T), e]

end Abstract

theorem exists_anti {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, hc, -, hs⟩ := h
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hv : v.IsComplex := hc.isComplex v
  have hsq : ∀ x, σ (σ x) = x := fun x => v.embedding.injective (by rw [hs, hs]; simp)
  have hx : ∃ x, σ x ≠ x := by
    by_contra hn
    push_neg at hn
    apply NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hv
    rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hs v.embedding x
    rw [hn] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hx
  exact ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), by rw [map_sub, hsq]; abel⟩

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol

variable {D : D7} {n : ℕ}

theorem cA_incA (D : D7) (x : D.host.E) : cA D (incA D x) = incA D (D.sp.cm.sig x) := by
  simp [cA, sigR, incA, inclR]

theorem hermPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ hermA D n) :
    hermPart D n (c • s) = 0 := by
  have h : adj s = s := hs
  rw [hermPart, adj_smul, h, hc, neg_smul, add_neg_cancel, smul_zero]

theorem hermPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    hermPart D n x + d • hermPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [hermPart, hermPart, adj_smul, he, neg_smul, ← sub_eq_add_neg, ← smul_sub, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  exact (add_add_sub_cancel _ _ _).trans (half_smul_add x)



def mulCE (d e : AE D) (hde : d * e = 1) : Mx D n n ≃ₜ+ Mx D n n where
  toFun x := d • x
  invFun x := e • x
  left_inv x := by
    change e • d • x = x
    rw [smul_smul, mul_comm, hde, one_smul]
  right_inv x := by
    change d • e • x = x
    rw [smul_smul, hde, one_smul]
  map_add' := smul_add d
  continuous_toFun := continuous_const_smul d
  continuous_invFun := continuous_const_smul e

def hermPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (hermPart D n) hermPart_add


theorem val_det_ad_inv (a : GL (Fin n) (AE D)) :
    ((Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) : AE D) = cA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  change (adj a.1 : Mx D n n).det = cA D a.1.det
  rw [adj, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem absA_det_ad_inv (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := by
  have h : (Matrix.GeneralLinearGroup.det ((ad a)⁻¹ : GL (Fin n) (AE D)) : (AE D)ˣ) =
      conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) := Units.ext (val_det_ad_inv a)
  rw [h]
  exact GlobalTheory.DiagThetaRule.absA_conj D _

theorem exists_anti_units (D : D7) : ∃ d e : AE D, d * e = 1 ∧ cA D d = -d ∧ cA D e = -e := by
  obtain ⟨δ, hδ, hσ⟩ := exists_anti _ (isCMExt_host D)
  refine ⟨incA D δ, incA D δ⁻¹, ?_, ?_, ?_⟩
  · rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  · rw [cA_incA, hσ, map_neg]
  · rw [cA_incA, map_inv₀, hσ, inv_neg, map_neg]

theorem lr_herm (a : GL (Fin n) (AE D)) : ∀ s ∈ hermA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ hermA D n :=
  fun s hs => (cg a ⟨s, hs⟩).2

theorem lr_herm_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ hermA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ hermA D n :=
  fun s hs => (cg a⁻¹ ⟨s, hs⟩).2

theorem lr_smul (a : GL (Fin n) (AE D)) (d e : AE D) (hde : d * e = 1) (x : Mx D n n) :
    GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ (mulCE d e hde x) = mulCE d e hde (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ x) := by
  change a.1 * (d • x) * ((ad a)⁻¹ : GL (Fin n) (AE D)).1 = d • (a.1 * x * ((ad a)⁻¹ : GL (Fin n) (AE D)).1)
  rw [Matrix.mul_smul, Matrix.smul_mul]



theorem integral_cg : ∀ (D : D7) (n : ℕ) (lam : Measure (hermA D n)), lam.IsAddHaarMeasure → ∀ (a : GL (Fin n) (AE D)) (f : hermA D n → ℂ), ∫ c, f (GlobalTheory.CompanionTheory.IwaAd.cg a c) ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ c, f c ∂lam := by
  intro D n lam hlam a f
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (isClosed_hermA (D := D) (r := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (hermA D n) (hermPartHom D n) continuous_hermPart hermPart_mem
    (fun s hs => hermPart_of_mem hs) (mulCE d e hde)
    (fun s hs => hermPart_anti hd hs) (fun s hs => hermPart_anti he hs)
    (fun x => hermPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_herm a) (lr_herm_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h : ∫ c, f (cg a c) ∂lam = _ := integral_comp_char lam (restr (hermA D n) _ (lr_herm a) (lr_herm_symm a)) f
  rw [h, hT, npow_neg_nat (absA_pos _) n]

end GlobalTheory.CompanionTheory.CgMod
end
end
