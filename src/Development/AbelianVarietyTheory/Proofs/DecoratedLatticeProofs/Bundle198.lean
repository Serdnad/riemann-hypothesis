module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

def ellA (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i => innerₛₗ ℂ (a i))

theorem ellA_tprod (a b : ∀ i, E i) : ellA a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪a i, b i⟫_ℂ := by
  simp [ellA]

theorem prod_inner_update [DecidableEq ι] (a b : ∀ i, E i) (i : ι) (z : E i) :
    ∏ j, ⟪Function.update a i z j, b j⟫_ℂ = ⟪z, b i⟫_ℂ * ∏ j ∈ Finset.univ \ {i}, ⟪a j, b j⟫_ℂ := by
  have : (fun j => ⟪Function.update a i z j, b j⟫_ℂ) = Function.update (fun j => ⟪a j, b j⟫_ℂ) i ⟪z, b i⟫_ℂ := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]

theorem ellA_update_add [DecidableEq ι] (a : ∀ i, E i) (i : ι) (x y : E i) :
    ellA (Function.update a i (x + y)) = ellA (Function.update a i x) + ellA (Function.update a i y) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, ellA_tprod, prod_inner_update, inner_add_left, add_mul]

theorem ellA_update_smul [DecidableEq ι] (a : ∀ i, E i) (i : ι) (c : ℂ) (x : E i) :
    ellA (Function.update a i (c • x)) = conj c • ellA (Function.update a i x) := by
  apply PiTensorProduct.ext
  ext b
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.smul_apply, ellA_tprod, prod_inner_update, inner_smul_left, smul_eq_mul, mul_assoc]

def ellC (a : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ :=
  (starLinearEquiv ℂ : ℂ ≃ₗ⋆[ℂ] ℂ).toLinearMap.comp (ellA a)

theorem ellC_apply (a : ∀ i, E i) (w : ⨂[ℂ] i, E i) : ellC a w = conj (ellA a w) := rfl

theorem ellC_tprod (a b : ∀ i, E i) : ellC a (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  rw [ellC_apply, ellA_tprod, map_prod]; simp

def ellM : (∀ i, E i) →ₘₗ[ℂ] ((⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ) where
  toFun := ellC
  map_update_add' a i x y := by
    ext w; simp [ellC_apply, ellA_update_add]
  map_update_smul' a i c x := by
    ext w; simp [ellC_apply, ellA_update_smul]

def ipT : (⨂[ℂ] i, E i) →ₗ[ℂ] (⨂[ℂ] i, E i) →ₗ⋆[ℂ] ℂ := PiTensorProduct.lift ellM

theorem ipT_tprod (a b : ∀ i, E i) :
    ipT (PiTensorProduct.tprod ℂ a) (PiTensorProduct.tprod ℂ b) = ∏ i, ⟪b i, a i⟫_ℂ := by
  simp [ipT, ellM, ellC_tprod]

theorem ipT_herm (w w' : ⨂[ℂ] i, E i) : ipT w w' = conj (ipT w' w) := by
  induction w using PiTensorProduct.induction_on generalizing w' with
  | smul_tprod r a =>
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, ipT_tprod, smul_eq_mul, map_mul, map_prod, inner_conj_symm,
        RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
      ring
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  | add x y hx hy => simp [map_add (f := _), LinearMap.add_apply, hx, hy]

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem ipT_map {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
    (f : ∀ i, G i →ₗ[ℂ] E i) (hf : ∀ i x y, ⟪f i x, f i y⟫_ℂ = ⟪x, y⟫_ℂ) (x y : ⨂[ℂ] i, G i) :
    ipT (PiTensorProduct.map f x) (PiTensorProduct.map f y) = ipT x y := by
  induction x using PiTensorProduct.induction_on generalizing y with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, PiTensorProduct.map_tprod, ipT_tprod, hf]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]

theorem ipT_pos_fd [∀ i, FiniteDimensional ℂ (E i)] (x : ⨂[ℂ] i, E i) (hx : x ≠ 0) : 0 < (ipT x x).re := by
  classical
  let e := fun i => stdOrthonormalBasis ℂ (E i)
  let B := Basis.piTensorProduct fun i => (e i).toBasis
  have hB : ∀ p q, ipT (B p) (B q) = if p = q then 1 else 0 := by
    intro p q
    simp only [B, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis, ipT_tprod]
    split_ifs with h
    · subst h; simp [OrthonormalBasis.inner_eq_ite]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [OrthonormalBasis.inner_eq_ite, Ne.symm hi])
  set c := B.repr x
  have hsum : ipT x x = ∑ p, c p * conj (c p) := by
    conv_lhs => rw [← B.sum_repr x]

    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul]
    simp [Finset.mul_sum, c]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hc : c ≠ 0 := by
    intro h; apply hx
    rw [← B.sum_repr x]; simp [c] at h; simp [h]
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hc (Finsupp.ext h)
  rw [hsum, Complex.re_sum]
  refine Finset.sum_pos' (fun q _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
  · rw [Complex.mul_conj]; simp [Complex.normSq_nonneg]
  · rw [Complex.mul_conj]; simpa using Complex.normSq_pos.mpr hp

end GlobalTheory.PiTensorInner

noncomputable section

namespace GlobalTheory.PiTensorInner

variable {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

theorem exists_fd (w : ⨂[ℂ] i, E i) : ∃ F : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (F i)) ∧
    ∃ w₀ : ⨂[ℂ] i, F i, PiTensorProduct.map (fun i => (F i).subtype) w₀ = w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    refine ⟨fun i => ℂ ∙ a i, fun i => inferInstance, r • PiTensorProduct.tprod ℂ (fun i => ⟨a i, Submodule.mem_span_singleton_self _⟩), ?_⟩
    simp
  | add x y hx hy =>
    obtain ⟨F₁, h₁, x₀, rfl⟩ := hx
    obtain ⟨F₂, h₂, y₀, rfl⟩ := hy
    refine ⟨fun i => F₁ i ⊔ F₂ i, fun i => inferInstance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : F₁ i ≤ F₁ i ⊔ F₂ i)) x₀ +
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : F₂ i ≤ F₁ i ⊔ F₂ i)) y₀, ?_⟩
    rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    rfl

theorem ipT_pos (w : ⨂[ℂ] i, E i) (hw : w ≠ 0) : 0 < (ipT w w).re := by
  obtain ⟨F, hF, w₀, rfl⟩ := exists_fd w
  have h0 : w₀ ≠ 0 := by rintro rfl; exact hw (map_zero _)
  rw [ipT_map (fun i => (F i).subtype) (fun i x y => rfl)]
  exact ipT_pos_fd w₀ h0

end GlobalTheory.PiTensorInner

namespace GlobalTheory.ChainOnto

theorem exists_ipD_smT : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ,
    (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧
    (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  intro D V S M
  exact ⟨GlobalTheory.PiTensorInner.ipT, fun v v' => GlobalTheory.PiTensorInner.ipT_tprod v v', GlobalTheory.PiTensorInner.ipT_herm,
    GlobalTheory.PiTensorInner.ipT_pos⟩

end GlobalTheory.ChainOnto
end
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.ChainOnto.TameRes

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_ltOne (P : HeightOneSpectrum (𝓞 E)) :
    IsOpen {z : P.adicCompletion E | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion E) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (k : E) :
    Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem valuation_eq_one_of_not_mem (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.mp fun h => hs ((P.valuation_lt_one_iff_mem s).mp h))

theorem locK_eq_one (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (c : (kP PP)ˣ →* ℂˣ)
    (hc : IsRes H PP c) (k : D.host.Eˣ) (hk : PP.valuation D.host.E ((k : D.host.E) - 1) < 1) :
    H.locK PP k = 1 := by
  have hv1 : PP.valuation D.host.E (k : D.host.E) = 1 := by
    have e : (k : D.host.E) = 1 + ((k : D.host.E) - 1) := by ring
    have h1 : PP.valuation D.host.E ((k : D.host.E) - 1) < PP.valuation D.host.E 1 := by rwa [map_one]
    rw [e]
    first
      | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : D.host.E) hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := by
    intro hm
    have hlt : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) < 1 :=
      (PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm
    exact absurd hav (ne_of_lt hlt)
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hdiff : a - (s : 𝓞 D.host.E) ∈ PP.asIdeal := by
    apply (PP.valuation_lt_one_iff_mem (K := D.host.E) _).mp
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E (a - (s : 𝓞 D.host.E))) < 1
    rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
    exact hk
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hms : (Ideal.Quotient.mk PP.asIdeal (s : 𝓞 D.host.E) : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hms
  let u : (kP PP)ˣ := Units.mkOfMulEqOne _ b hb
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ks : D.host.Eˣ := Units.mk0 _ hs0
  have e1 : c u = H.locK PP ks := hc (s : 𝓞 D.host.E) ks u rfl rfl
  have e2 : c u = H.locK PP ka := hc a ka u rfl (Ideal.Quotient.eq.mpr hdiff).symm
  have hk' : k = ka * ks⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hk', map_mul, map_inv, ← e1, ← e2, mul_inv_cancel]

theorem tameAt_of_isRes : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ),
    IsRes H PP a → H.TameAt PP := by
  intro D H PP c hc
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion D.host.E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion D.host.E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion D.host.E | Valued.v (z - 1) < 1}) :=
    hT.inter ((isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation D.host.E (k - 1) < 1 := by
    rw [← val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := locK_eq_one D H PP c hc (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end GlobalTheory.ChainOnto.TameRes
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelWithP

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levelCharacter_withLevel_of_mem {P : LevelP L.Pg L.r ℂ} {κ : GA D V} (hp : rTup β L (Lev.finE V κ) ∈ P.H) :
    Lev.levChi V β (Lev.withP L P) κ = ((P.chi ⟨_, hp⟩ : ℂˣ) : ℂ) * Lev.levChi V β (Lev.flagL L) κ := by
  unfold Lev.levChi
  rw [Lev.levFn_withP, extendOne_of_mem _ hp, Units.val_mul]

theorem hasType_withCharacter_iff (P : LevelP L.Pg L.r ℂ) (F : GA D V → ℂ) :
    Lev.HasType V β (Lev.withP L P) F ↔ Lev.HasType V β (Lev.flag1L L) F ∧
      ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ g,
        (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * F (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F g := by
  constructor
  · intro h
    refine ⟨fun κ hκ g => ?_, fun p κ hκ g => ?_⟩
    · have h1 : rTup β L (Lev.finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
      have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [h1]; exact P.H.one_mem
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      rw [h κ hw g]
      congr 1
      rw [levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = 1 := Subtype.ext h1
      rw [e, map_one, Units.val_one, one_mul]
      unfold Lev.levChi
      rw [Lev.levFn_flag1]
    · have hp : rTup β L (Lev.finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
      have hw : κ ∈ Lev.levG V β (Lev.withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
      have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
      rw [h κ hw g, levelCharacter_withLevel_of_mem hp]
      have e : (⟨_, hp⟩ : P.H) = p := Subtype.ext hκ.2.2
      rw [e, inv_mul_eq_iff_eq_mul₀ hne]
      ring
  · rintro ⟨-, h⟩ κ hκ g
    have hp : rTup β L (Lev.finE V κ) ∈ P.H := hκ.2.2
    have hl : Lev.IsLevelLift V β L (⟨_, hp⟩ : P.H).1 κ := ⟨hκ.1, hκ.2.1, rfl⟩
    have key := h ⟨_, hp⟩ κ hl g
    have hne := Lev.levChi_ne_zero (β := β) (Lev.flagL L) κ
    rw [inv_mul_eq_iff_eq_mul₀ hne] at key
    rw [key, levelCharacter_withLevel_of_mem hp]
    ring

end GlobalTheory.ChainOnto.LevelWithP


open GlobalTheory.ChainOnto.LevelWithP in
theorem GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (T : SmT M →ₗ[ℂ] (GA D V → ℂ)), T ∈ MultT θ M (levS V β (Lev.withP L P)) (Lev.levChi V β (Lev.withP L P)) ↔ T ∈ MultT θ M (levS V β (Lev.flag1L L)) (Lev.levChi V β (Lev.flag1L L)) ∧ ∀ (p : P.H) κ, Lev.IsLevelLift V β L p.1 κ → ∀ w g, (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * T w g := by
  intro D θ V S M β L P T
  rw [mem_multT, mem_multT, GlobalTheory.MultMem.mem_mult_iff, GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · intro h
    have hT : ∀ v, Lev.HasType V β (Lev.withP L P) (PiTensorProduct.lift.symm T v) := fun v κ hκ g => h.lev v κ hκ g
    refine ⟨⟨h.aut, h.cusp, fun v κ hκ g => ((hasType_withCharacter_iff P _).1 (hT v)).1 κ hκ g, h.equiv, h.cont⟩, ?_⟩
    intro p κ hκ w g
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have key : (Lev.levChi V β (Lev.flagL L) κ)⁻¹ * T (PiTensorProduct.tprod ℂ v) (g * κ) =
          ((P.chi p : ℂˣ) : ℂ) * T (PiTensorProduct.tprod ℂ v) g := ((hasType_withCharacter_iff P _).1 (hT v)).2 p κ hκ g
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      linear_combination r * key
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply]
      linear_combination hx + hy
  · rintro ⟨h, hP⟩
    refine ⟨h.aut, h.cusp, fun v κ hκ g => ?_, h.equiv, h.cont⟩
    refine (hasType_withCharacter_iff P _).2 ⟨fun κ hκ g => h.lev v κ hκ g, fun p κ' hκ' g' => ?_⟩ κ hκ g
    exact hP p κ' hκ' _ g'

end
end
