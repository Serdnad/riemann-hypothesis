module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
public import ReciprocityTheory.DualLattices.Bundle008
public import ReciprocityTheory.DualLattices.Bundle012
public import ReciprocityTheory.DualLattices.Bundle020
public import ReciprocityTheory.DualLattices.FormalChartAtZero
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.ColengthSqMulLe
public import ReciprocityTheory.DualLattices.ValuationPairwiseDifferenceProductPowLeColengthS
public import ReciprocityTheory.DualLattices.Bundle019
import ReciprocityTheory.DualLattices.Bundle017
public import ReciprocityTheory.DualLattices.InstAddCommMonoidFibreFst
public import ReciprocityTheory.DualLattices.NilSurjOfSqZero
public import ReciprocityTheory.DualLattices.TotalFibreMapTotalFibreNsmulSnd
public import ReciprocityTheory.DualLattices.ProdDvdOfIso
public import ReciprocityTheory.DualLattices.UpSmith

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] {v : Valuation C NNReal}

def blkLat {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) where
  B := Matrix.of fun x y => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0
  det_ne := by
    have h : (Matrix.of fun x y : Fin n × Fin s => if x.1 = y.1 then (Ls x.1).B x.2 y.2 else 0) =
        (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
      ext x y
      simp [Matrix.blockDiagonal_apply, eq_comm]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Ls τ).det_ne

lemma blkLat_det {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) :
    (blkLat Ls).B.det = ∏ τ, (Ls τ).B.det := by
  have h : (blkLat Ls).B =
      (Matrix.blockDiagonal fun τ => (Ls τ).B).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext x y
    simp [blkLat, Matrix.blockDiagonal_apply, eq_comm]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]

lemma blkLat_pts {n s : ℕ} (Ls : Fin n → Lat v (Fin s)) : (blkLat Ls).pts = sumPts Ls := by
  have hmv : ∀ c : Fin n × Fin s → C, (blkLat Ls).B *ᵥ c =
      fun y => ((Ls y.1).B *ᵥ fun j => c (y.1, j)) y.2 := by
    intro c
    ext ⟨τ, i⟩
    simp only [blkLat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul]
    rw [Finset.sum_eq_single τ]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  ext w
  simp only [ReciprocityTheory.PGsh.Lat.pts, sumPts, Set.mem_setOf_eq, hmv]
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    exact ⟨fun j => c (τ, j), fun j => hc (τ, j), rfl⟩
  · intro hw
    choose c hc hce using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext y
    exact congrFun (hce y.1) y.2

lemma colen_blk {n s : ℕ} (L's Ls : Fin n → Lat v (Fin s)) :
    colen (blkLat L's) (blkLat Ls) = ∏ τ, colen (L's τ) (Ls τ) := by
  simp only [ReciprocityTheory.PGsh.colen, blkLat_det, map_prod]
  rw [Finset.prod_div_distrib]

theorem colength_sq_mul_le_prod (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) :
    colen M' M ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s := by
  have hdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι), v L.B.det ≠ 0 :=
    fun L => (map_ne_zero v).2 L.det_ne
  set S : Lat v (Fin n × Fin s) := blkLat Mτ
  set S' : Lat v (Fin n × Fin s) := blkLat M'τ
  have h2 := valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hMst hMτ (blkLat_pts Mτ)
  have h3 := colength_sq_mul_le a hinj hint s h A F M' S' M'τ hF hM' hM'τ (blkLat_pts M'τ)
  have hP : colen S' S = ∏ τ, colen (M'τ τ) (Mτ τ) := colen_blk M'τ Mτ
  have hid : colen M' M * colen M S = colen M' S' * colen S' S := by
    simp only [ReciprocityTheory.PGsh.colen]
    rw [div_mul_div_cancel₀ (hdet M), div_mul_div_cancel₀ (hdet S')]
  have hc : 0 < colen M S ^ 2 := by
    have : colen M S ≠ 0 := div_ne_zero (hdet M) (hdet S)
    positivity
  rw [← hP]
  refine le_of_mul_le_mul_right ?_ hc
  calc colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2
      = colen M' S' ^ 2 * v (discr a) ^ h * colen S' S ^ 2 := by
        rw [show colen M' M ^ 2 * v (discr a) ^ h * colen M S ^ 2 =
          (colen M' M * colen M S) ^ 2 * v (discr a) ^ h by ring, hid]; ring
    _ ≤ v (discr a) ^ (2 * s) * colen S' S ^ 2 := by gcongr
    _ = colen S' S ^ 2 * v (discr a) ^ s * v (discr a) ^ s := by ring
    _ ≤ colen S' S ^ 2 * v (discr a) ^ s * colen M S ^ 2 := by gcongr

end ReciprocityTheory.PGsh.Up
end
end

section

namespace ReciprocityTheory.PGsh.L2

theorem h3 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩

end ReciprocityTheory.PGsh.L2
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

theorem tangentPairingStatement_of_heightFunctional (hB2 : HighestWeightVectorUniformBounds B) : TangentPairingStatement B := by
  intro R' R π ξ Dp N hsurj hker hsq _ hN sh th Vs Vt hs ht zh z hsV htV hhs hht hpair hz
  have hπ : π.SqZero := π.sqZero_of_span ξ hsurj hker hsq
  obtain ⟨O, hOsw, hO⟩ := B.step1 π Dp ξ hsurj hker hsq hB2 N hN
  obtain ⟨hsN, htN, u0, l1, l2, h1, h2, hz'⟩ := hpair
  obtain ⟨l⟩ := B.nonempty R' sh th
  obtain ⟨μ, hμ⟩ := B.exists_smul (B.pmap π l) u0
  obtain ⟨μ', hμ'⟩ := π.exists_unit_lift hsurj μ
  obtain ⟨a1, ha1⟩ := π.exists_unit_lift hsurj l1
  obtain ⟨a2, ha2⟩ := π.exists_unit_lift hsurj l2
  obtain ⟨l', hl⟩ : ∃ l' : B.P R' sh th, B.pmap π l' = u0 :=
    ⟨B.smul μ' l, by rw [B.pmap_smul, hμ', hμ]⟩
  have htg0 : ∀ V, B.map π (B.tg π hπ V) = 0 := fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩
  have hinv1 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a1⁻¹ * l1 = 1 := by
    rw [map_inv, ha1, inv_mul_cancel]
  have hinv2 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a2⁻¹ * l2 = 1 := by
    rw [map_inv, ha2, inv_mul_cancel]

  have hu : HEq (B.pmap π (B.smul a1⁻¹ (B.tr1 hsV (B.nsmul1 l' N))))
      (B.zero1 (B.map π th)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr1 hsV (B.nsmul1 l' N))) (B.smul l1 (B.zero1 (B.map π th))) := by
      refine (B.pmap_hcongr π hsV.symm rfl (B.castFst_heq hsV _)).trans ?_
      refine (B.pmap_nsmul1 π _ N).trans ?_
      rw [hl, ← h1]
      exact (B.castFst_heq hsN _).symm
    refine (B.smul_hcongr (htg0 Vs) rfl _ e).trans ?_
    rw [← B.mul_smul, hinv1, B.one_smul]
  have hu'0 : HEq (B.pmap π (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))))
      (B.zero2 (B.map π sh)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr2 htV (B.nsmul2 l' N))) (B.smul l2 (B.zero2 (B.map π sh))) := by
      refine (B.pmap_hcongr π rfl htV.symm (B.castSnd_heq htV _)).trans ?_
      refine (B.pmap_nsmul2 π _ N).trans ?_
      rw [hl, ← h2]
      exact (B.castSnd_heq htN _).symm
    refine (B.smul_hcongr rfl (htg0 Vt) _ e).trans ?_
    rw [← B.mul_smul, hinv2, B.one_smul]
  have hu' : HEq (B.pmap π (B.sw (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N)))))
      (B.zero1 (B.map π sh)) := by
    rw [← B.sw_nat]
    refine (B.sw_hcongr rfl (htg0 Vt) hu'0).trans ?_
    rw [B.sw_zero2]
  obtain ⟨ct, hct, hNt⟩ := hO Vs Vt th ht htV hht _ hu
  obtain ⟨cs, hcs, hNs⟩ := hO Vt Vs sh hs hsV hhs _ hu'

  have k1 : HEq (B.smul (a1⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul ct (O Vs Vt)) := by
    refine HEq.trans ?_ ((B.castSnd_heq htV _).symm.trans (heq_of_eq hNt))
    rw [B.nsmul2_smul]
    exact B.smul_hcongr hsV rfl _ (B.nsmul2_hcongr hsV rfl N (B.castFst_heq hsV _).symm)
  have k2 : HEq (B.smul (a2⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul cs (O Vs Vt)) := by
    have s1 : HEq (B.sw (B.nsmul1 (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))) N))
        (B.smul cs (O Vt Vs)) := by
      rw [B.sw_nsmul1]; exact (B.castSnd_heq hsV _).symm.trans (heq_of_eq hNs)
    have s2 := B.sw_hcongr rfl hsV s1
    rw [B.sw_sw, B.sw_smul, hOsw] at s2
    refine HEq.trans ?_ s2
    rw [B.nsmul1_smul, B.nsmul_comm]
    exact B.smul_hcongr rfl htV _ (B.nsmul1_hcongr rfl htV N (B.castSnd_heq htV _).symm)
  obtain ⟨X₀, hX₀⟩ := B.exists_cast hsV htV (B.nsmul2 (B.nsmul1 l' N) N)
  have e1 : B.smul (a1⁻¹ ^ N) X₀ = B.smul ct (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k1)
  have e2 : B.smul (a2⁻¹ ^ N) X₀ = B.smul cs (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k2)
  have hX1 : X₀ = B.smul (a1 ^ N * ct) (O Vs Vt) := by
    rw [B.mul_smul, ← e1, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have hX2 : X₀ = B.smul (a2 ^ N * cs) (O Vs Vt) := by
    rw [B.mul_smul, ← e2, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have key : a1 ^ N * ct = a2 ^ N * cs := B.smul_inj (hX1.symm.trans hX2)

  have hν : Units.map (π.1 : (R' : Type u) →* (R : Type u)) (zh * a2 * a1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hz, ha1, ha2, hz', div_mul_cancel, mul_inv_cancel]
  have hνN := LHom.pow_eq_one hπ hN (zh * a2 * a1⁻¹)
    (by have := congrArg Units.val hν; simpa using this)
  have hz1 : zh ^ N * a2 ^ N = a1 ^ N := by
    rw [mul_pow, mul_pow, inv_pow] at hνN
    exact mul_inv_eq_one.1 hνN
  have hz2 : zh ^ N * ct = cs := by
    have h3 : a2 ^ N * (zh ^ N * ct) = a2 ^ N * cs := by
      rw [← key, ← hz1]; ac_rfl
    exact mul_left_cancel h3
  have hA : π.1 (B.evK π ht Vs) = 0 := (RingHom.mem_ker).1 (evalT_mem ht (RingHom.ker π.1) Vs)
  have hB : π.1 (B.evK π hs Vt) = 0 := (RingHom.mem_ker).1 (evalT_mem hs (RingHom.ker π.1) Vt)
  have hAA := LHom.mul_eq_zero hπ hA hA
  have hAB := LHom.mul_eq_zero hπ hA hB
  have h4 := congrArg Units.val hz2
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hct, hcs] at h4
  linear_combination (1 + B.evK π ht Vs) * h4 + (zh : (R' : Type u)) ^ N * hAA - hAB

end BX

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

namespace Tot

section len

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_pi {m : ℕ} (M : Fin m → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (X : Fin m → NNReal) (h : ∀ i, HasLen v R (M i) (X i)) :
    HasLen v R ((i : Fin m) → M i) (∏ i, X i) := by
  classical
  choose n c he hX using h
  let e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j}) := fun i => (he i).some
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩
  · exact (LinearEquiv.piCongrRight e).trans
      ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans
        (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)
  · rw [Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2)))
      (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => hX i

end len

variable {R : Type} [CommRing R]

theorem sum_fromBlocks_diag {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fromBlocks_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add,
      add_zero]

theorem sum_mulVec' {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

end Tot

open Tot in
theorem eigenLengthProductStatement_holds : EigenLengthProductStatement := by
  intro C _ v R _ _ hv g m Ht Bt εT εL π hπ hTo hTs hLo hLs hHt hBt X hX
  classical
  set Φ := fromRows Ht Bt with hΦ
  set Pm : Fin m → Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fun i => fromBlocks ((εL (π i))ᵀ) 0 0 (εL i) with hPm
  have hPmv : ∀ i w, Pm i *ᵥ w =
      Sum.elim ((εL (π i))ᵀ *ᵥ (w ∘ Sum.inl)) (εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    simp only [hPm, fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  have hmem : ∀ i w, Pm i *ᵥ w ∈ qE εL i (π i) := by
    intro i w
    refine Submodule.mem_inf.2 ⟨⟨w ∘ Sum.inl, ?_⟩, ⟨w ∘ Sum.inr, ?_⟩⟩
    · show (εL (π i))ᵀ *ᵥ (w ∘ Sum.inl) = (Pm i *ᵥ w) ∘ Sum.inl
      rw [hPmv]; rfl
    · show εL i *ᵥ (w ∘ Sum.inr) = (Pm i *ᵥ w) ∘ Sum.inr
      rw [hPmv]; rfl
  have hsel : ∀ i k w, w ∈ qE εL i (π i) → Pm k *ᵥ w = if k = i then w else 0 := by
    intro i k w hw
    obtain ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := Submodule.mem_inf.1 hw
    have e1 : w ∘ Sum.inl = (εL (π i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = εL i *ᵥ y2 := hy2.symm
    rw [hPmv, e1, e2, mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hLo, hLo]
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      rw [← e1, ← e2, Sum.elim_comp_inl_inr]
    · have hne : π i ≠ π k := fun h => hki (π.injective h).symm
      simp only [hki, hne, if_false, transpose_zero, zero_mulVec]
      ext s; cases s <;> rfl
  have hT : ∑ i, (εL (π i))ᵀ = 1 := by
    rw [← transpose_sum, Equiv.sum_comp π εL, hLs, transpose_one]
  have hPsum : ∑ i, Pm i = 1 := by
    simp only [hPm]
    rw [sum_fromBlocks_diag, hT, hLs, fromBlocks_one]
  have hsum : ∀ w, ∑ i, Pm i *ᵥ w = w := by
    intro w
    rw [← sum_mulVec', hPsum, one_mulVec]
  have hPΦ : ∀ i, Pm i * Φ = Φ * εT i := by
    intro i
    rw [hΦ, hPm, fromBlocks_mul_fromRows, fromRows_mul, Matrix.zero_mul, Matrix.zero_mul, add_zero,
      zero_add,
      hHt, hBt]
  set Ψ : (Fin g ⊕ Fin g → R) →ₗ[R] ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
      LinearMap.codRestrict (qE εL i (π i)) (mulVecLin (Pm i)) (hmem i) with hΨdef
  have hΨ : ∀ w i, Ψ w i = Submodule.Quotient.mk ⟨Pm i *ᵥ w, hmem i w⟩ := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    intro q
    choose w hw using fun i => Submodule.Quotient.mk_surjective _ (q i)
    refine ⟨∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R), funext fun k => ?_⟩
    rw [hΨ, ← hw k]
    congr 1
    apply Subtype.ext
    show Pm k *ᵥ ∑ i, ((w i : qE εL i (π i)) : Fin g ⊕ Fin g → R) = (w k : Fin g ⊕ Fin g → R)
    rw [mulVec_sum]
    simp only [fun i => hsel i k _ (w i).2]
    simp
  have hker : LinearMap.ker Ψ = LinearMap.range (mulVecLin Φ) := by
    ext w
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      have hi : ∀ i, ∃ t, Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ w := by
        intro i
        have := congrFun h i
        rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨y, ⟨t, rfl⟩, hy⟩ := this
        exact ⟨t, hy⟩
      choose t ht using hi
      refine ⟨∑ i, εT i *ᵥ t i, ?_⟩
      show Φ *ᵥ ∑ i, εT i *ᵥ t i = w
      rw [mulVec_sum]
      simp only [ht]
      exact hsum w
    · rintro ⟨t, rfl⟩
      funext i
      rw [hΨ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
      show Φ *ᵥ (εT i *ᵥ t) = Pm i *ᵥ (Φ *ᵥ t)
      rw [mulVec_mulVec, mulVec_mulVec, hPΦ]
  have iso : ((Fin g ⊕ Fin g → R) ⧸ LinearMap.range (mulVecLin Φ)) ≃ₗ[R]
      ((i : Fin m) → xModE Ht Bt εT εL π i) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hsurj)
  set e : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he
  set Φ' := reindex e e Φ with hΦ'
  have hdet : Φ'.det = Φ.det := det_reindex_self e Φ
  set F : (Fin (g + g) → R) ≃ₗ[R] (Fin g ⊕ Fin g → R) := LinearEquiv.funCongrLeft R R e with hF
  have hFapp : ∀ y, F y = y ∘ e := fun y => rfl
  have hcomm : ∀ y, F (Φ' *ᵥ y) = Φ *ᵥ F y := by
    intro y
    rw [hFapp, hFapp, hΦ', reindex_apply, submatrix_mulVec_equiv]
    ext s
    simp
  have hmap : (LinearMap.range (mulVecLin Φ')).map F.toLinearMap = LinearMap.range (mulVecLin Φ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨F y, (hcomm y).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨Φ' *ᵥ F.symm t, ⟨F.symm t, rfl⟩, ?_⟩
      show F (Φ' *ᵥ F.symm t) = Φ *ᵥ t
      rw [hcomm, LinearEquiv.apply_symm_apply]
  have hcok := Submodule.Quotient.equiv _ _ F hmap
  have hL1 := Smith.hasLen_coker_det (C := C) (v := v) hv Φ'
  have hL2 : HasLen v R ((Fin (g + g) → R) ⧸ LinearMap.range (mulVecLin Φ')) (∏ i, X i) :=
    hasLen_equiv (hcok.trans iso) (hasLen_pi _ X hX)
  rw [hasLen_unique hv hL2 hL1, hdet]

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def nsmulF {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a : Fin g → S) : ℕ → Fin g → S
  | 0 => 0
  | n + 1 => fAdd F (nsmulF F a n) a

def PSerFrobStatement (p : ℕ) [Fact p.Prime] (K : LAlg R₀) (ch : FormalChartAtZero B K g) : Prop :=
  ∀ N : ℕ, ∃ G : Fin g → MvPolynomial (Fin g) R₀,
    (∀ k m, (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff (G k) m = p * r) ∧
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
      nsmulF ch.F a p = fun k => MvPolynomial.aeval a (G k)

end ReciprocityTheory.PGsh.Be2
end
end
