module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.KWhit

theorem norm_det_bottom_block_sq :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ),
      ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ →
      tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) →
      g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det →
      ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 *
        (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  intro n _ _ t u D K₁ K₂ β h g e η he hη hK h1 h2 htu hh hβ hg hgdet
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖η‖ ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hsdef] at hg
  obtain ⟨M, hM⟩ : ∃ M : Matrix n n ℂ, M = g⁻¹ * h.map star * g⁻¹ᴴ := ⟨_, rfl⟩
  rw [← hM]
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hss : s * s = ‖η‖ ^ (-1 : ℝ) := by
    rw [hsdef, ← Real.rpow_add hn]
    norm_num
  have hs : s * s * ‖η‖ = 1 := by
    rw [hss, Real.rpow_neg_one, inv_mul_cancel₀ hn.ne']
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hinv : s⁻¹ = s * ‖η‖ := inv_eq_of_mul_eq_one_right (by linear_combination hs)
  have nsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  have hsstar : star (s : ℂ) = s := by
    exact Complex.conj_ofReal s
  have hsinvstar : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
    rw [star_inv₀, hsstar]
  have hee : e * star e = 1 := by
    rw [← nsq e, he]
    norm_num
  have hee' : star e * e = 1 := by rw [mul_comm]; exact hee
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsa : star (-(η * (s : ℂ))) = -(star η * (s : ℂ)) := by
    rw [star_neg, star_mul', hsstar]
  have ha : -(η * (s : ℂ)) * star (-(η * (s : ℂ))) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [hsa]
    have e1 : -(η * (s : ℂ)) * -(star η * (s : ℂ)) = (η * star η) * ((s : ℂ) * (s : ℂ)) := by
      ring
    rw [e1, ← nsq η]
    have e2 : ‖η‖ ^ 2 * (s * s) = s⁻¹ * s⁻¹ := by
      rw [hinv]
      ring
    have e3 : ((‖η‖ ^ 2 : ℝ) : ℂ) * ((s : ℂ) * (s : ℂ)) = ((‖η‖ ^ 2 * (s * s) : ℝ) : ℂ) := by
      first | (push_cast; ring) | push_cast | simp
    rw [e3, e2]
    first | (push_cast; ring) | push_cast | simp
  have ha' : star (-(η * (s : ℂ))) * -(η * (s : ℂ)) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [mul_comm]; exact ha
  have hs_ij : ∀ i j, star (h i j) = h j i := by
    intro i j
    have hx := congrArg (fun X : Matrix n n ℂ => X j i) hh
    simp only [Matrix.conjTranspose_apply] at hx
    exact hx
  have hT : h.map star = hᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hTH : hᵀᴴ = hᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hMH : Mᴴ = M := by
    rw [hM, hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTH, mul_assoc]
  have hgM : g * M = hᵀ * g⁻¹ᴴ := by
    rw [hM, hT, ← mul_assoc, ← mul_assoc, hgg, one_mul]
  have hut : uᴴ * t = 1 := by
    have hx := congrArg Matrix.conjTranspose htu
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] at hx
  have huH : uᴴ = (s : ℂ) • g⁻¹ := by
    calc uᴴ = g⁻¹ * (g * uᴴ) := by rw [← mul_assoc, hgg', one_mul]
      _ = (s : ℂ) • g⁻¹ := by rw [hg, mul_smul_comm, mul_one]
  have hu : u = (s : ℂ) • g⁻¹ᴴ := by
    calc u = uᴴᴴ := (Matrix.conjTranspose_conjTranspose u).symm
      _ = (s : ℂ) • g⁻¹ᴴ := by rw [huH, Matrix.conjTranspose_smul, hsstar]
  have ht : t = (s : ℂ)⁻¹ • g := by
    have h3 : (s : ℂ) • t = g := by
      calc (s : ℂ) • t = ((s : ℂ) • (1 : Matrix n n ℂ)) * t := by rw [smul_mul_assoc, one_mul]
        _ = g * uᴴ * t := by rw [hg]
        _ = g := by rw [mul_assoc, hut, mul_one]
    rw [← h3, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  have hβu : β * u = (-(η * (s : ℂ))) • (g * M) := by
    rw [hβ, hu, hgM, neg_mul, smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul]
  have hDD : D * Dᴴ = t * tᴴ + (β * u) * (β * u)ᴴ := by
    have step1 : D * Dᴴ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
      calc D * Dᴴ = D * (K₁ * K₁ᴴ + K₂ * K₂ᴴ) * Dᴴ := by rw [hK, mul_one]
        _ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
          simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
    rw [step1, ← h1, ← h2]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hee', one_smul]
  have hmain : D * Dᴴ = ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (g * (1 + M * M) * gᴴ) := by
    rw [hDD, ht, hβu]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsinvstar, ha']
    rw [← smul_add]
    congr 1
    simp only [Matrix.conjTranspose_mul, hMH, mul_add, add_mul, mul_one, mul_assoc]
  have hdet : D.det * star D.det = t.det * star t.det * (1 + M * M).det := by
    have lhs : D.det * star D.det = (D * Dᴴ).det := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [lhs, hmain, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      ht, Matrix.det_smul, star_mul', star_pow, hsinvstar]
    ring
  rw [← nsq, ← nsq] at hdet
  have hre := congrArg Complex.re hdet
  first
    | (rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre; exact hre)
    | (simpa [Complex.mul_re] using hre)

end GlobalTheory.CompanionTheory.KWhit
end

section

noncomputable section

open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

variable {n : ℕ}

section Ring

variable {R : Type} [CommRing R]

def nU (y : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks 1 y 0 1
  inv := fromBlocks 1 (-y) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def pM (a d : GL (Fin n) R) (b : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks a.1 b 0 d.1
  inv := fromBlocks (a⁻¹).1 (-((a⁻¹).1 * b * (d⁻¹).1)) 0 (d⁻¹).1
  val_inv := by
    simp [fromBlocks_multiply, ← fromBlocks_one, ← Matrix.mul_assoc]
  inv_val := by
    simp [fromBlocks_multiply, ← fromBlocks_one, Matrix.mul_assoc]

def lowerLeftBlock (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₁

def dBlk (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₂

end Ring

def iD {k : Type} [Field k] (g : GL (Ix n) k) : ℕ := n - (dBlk g).rank

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {L : Type} [Field L] [Algebra O L]

abbrev inL : GL (Ix n) O →* GL (Ix n) L := Matrix.GeneralLinearGroup.map (algebraMap O L)

abbrev resK : GL (Ix n) O →* GL (Ix n) (IsLocalRing.ResidueField O) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)

def scM (w : Lˣ) : GL (Fin n) L := Units.map (Matrix.scalar (Fin n) : L →+* Matrix (Fin n) (Fin n) L).toMonoidHom w

def tauM (w : Lˣ) : GL (Ix n) L := pM 1 (scM w) 0

def IsHgt (nv : Lˣ →* ℝ≥0) (h : GL (Ix n) L → ℝ≥0) : Prop :=
  ∀ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
    h (pM a d b * inL κ) = nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d)

def NvOK [Fintype (IsLocalRing.ResidueField O)] (nv : Lˣ →* ℝ≥0) (w : Lˣ) : Prop :=
  (∀ u : Oˣ, nv (Units.map (algebraMap O L).toMonoidHom u) = 1) ∧
    nv w = ((Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0))⁻¹

def IsRed (w : Lˣ) (κ : GL (Ix n) O) (hb : GL (Ix n) (IsLocalRing.ResidueField O)) : Prop :=
  ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ' : GL (Ix n) O),
    inL κ * tauM w = pM a d b * inL κ' ∧ resK κ' = hb

def Gam2 (ϖ : O) : Subgroup (GL (Ix n) O) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))).ker

instance (ϖ : O) : (Gam2 (n := n) ϖ).Normal := by unfold Gam2; infer_instance

def avgK (ϖ : O) (φ : GL (Ix n) O → ℂ) : ℂ :=
  (Nat.card (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) : ℂ)⁻¹ * ∑ᶠ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ, φ (Quotient.out u)

def liftM (ℓ : IsLocalRing.ResidueField O → O) (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) :
    Matrix (Fin n) (Fin n) L := (Y.map ℓ).map (algebraMap O L)

end Local

def coY {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (β Y : Matrix (Fin n) (Fin n) k) : ℂ :=
  ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β)))

end GlobalTheory.CompanionTheory.Jp

end
end

section

namespace GlobalTheory.CompanionTheory.CosetSum

theorem mem_of_translated_bumps : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  intro Γ J _ _ _ Q K K₁ π M Gf hle hidx hconj hdec htr hlawM hlaw hinv hb
  classical
  let H : Subgroup K := K₁.subgroupOf K
  haveI hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : Γ) ∈ K₁ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using hconj g g.2 n hn'⟩
  haveI : H.FiniteIndex := ⟨hidx⟩
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let P : Γ → Prop := fun x => ∃ q : Q, ∃ b ∈ K₁, x = (q : Γ) * b
  have hPmul : ∀ x, ∀ b ∈ K₁, P x → P (x * b) := by
    rintro x b hb' ⟨q, c, hc, rfl⟩
    exact ⟨q, c * b, K₁.mul_mem hc hb', by simp [mul_assoc]⟩
  have hb2 : ∀ κ : K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧
      ∀ g : Γ, (¬ P g) → φ g = 0 := fun κ => hb κ κ.2
  choose φ hφM hφ1 hφ0 using hb2
  have key : ∀ κ' κ : K, φ κ ((κ' : Γ) * (κ : Γ)⁻¹) =
      if P ((κ' : Γ) * (κ : Γ)⁻¹) then Gf κ' else 0 := by
    intro κ' κ
    split_ifs with h
    · obtain ⟨q, b, hbm, e⟩ := h
      rw [e, hφ1 κ q b hbm, ← hlaw]
      have hκ' : (κ' : Γ) = q * b * κ := by rw [← e]; group
      have e2 : (q : Γ) * κ = κ' * ((κ : Γ)⁻¹ * b⁻¹ * κ) := by rw [hκ']; group
      have hm : (κ : Γ)⁻¹ * b⁻¹ * κ ∈ K₁ := by
        simpa using hconj _ (K.inv_mem κ.2) _ (K₁.inv_mem hbm)
      rw [e2, hinv _ _ hm]
    · exact hφ0 κ _ h
  let r : K ⧸ H → K := Quotient.out
  have hr : ∀ δ : K ⧸ H, ((r δ : K) : K ⧸ H) = δ := fun δ => QuotientGroup.out_eq' δ
  have hPcl : ∀ x y : K, (x : K ⧸ H) = y → P x → P y := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    have hm' : (x : Γ)⁻¹ * y ∈ K₁ := by simpa using Subgroup.mem_subgroupOf.1 hm
    have := hPmul _ _ hm' hx
    simpa using this
  let Pd : K ⧸ H → Prop := fun ε => P (r ε)
  have hPd : ∀ x : K, P x ↔ Pd (x : K ⧸ H) := fun x =>
    ⟨hPcl _ _ (hr _).symm, hPcl _ _ (hr _)⟩
  let Φ : Γ → J := ∑ δ : K ⧸ H, (fun g => φ (r δ) (g * ((r δ : K) : Γ)⁻¹))
  have hΦM : Φ ∈ M := M.sum_mem fun δ _ => htr _ (hφM _) _
  let n : ℕ := (Finset.univ.filter Pd).card
  have hΦ : ∀ κ' : K, Φ κ' = n • Gf κ' := by
    intro κ'
    have h1 : Φ κ' = ∑ δ : K ⧸ H, if Pd ((κ' : K ⧸ H) * δ⁻¹) then Gf κ' else 0 := by
      simp only [Φ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [key]
      have hcl : (((κ' * (r δ)⁻¹ : K)) : K ⧸ H) = (κ' : K ⧸ H) * δ⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr]
      have := hPd (κ' * (r δ)⁻¹)
      rw [hcl] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simp only [this]
    rw [h1]
    have h2 := Equiv.sum_comp ((Equiv.inv (K ⧸ H)).trans (Equiv.mulLeft (κ' : K ⧸ H)))
      (fun ε => if Pd ε then Gf κ' else 0)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at h2
    rw [h2, ← Finset.sum_filter, Finset.sum_const]
  have hn : n ≠ 0 := by
    have h1 : Pd 1 := by
      have : (r 1 : Γ) ∈ K₁ := by
        have : r 1 ∈ H := (QuotientGroup.eq_one_iff _).1 (hr 1)
        exact Subgroup.mem_subgroupOf.1 this
      exact ⟨1, _, this, by simp⟩
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hΨM : (n : ℂ)⁻¹ • Φ ∈ M := M.smul_mem _ hΦM
  have hEq : (n : ℂ)⁻¹ • Φ = Gf := by
    funext g
    obtain ⟨q, κ, hκ, rfl⟩ := hdec g
    have hK : ((n : ℂ)⁻¹ • Φ) κ = Gf κ := by
      have := hΦ ⟨κ, hκ⟩
      simp only at this
      rw [Pi.smul_apply, this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [hlawM _ hΨM, hK, hlaw]
  exact hEq ▸ hΨM

end GlobalTheory.CompanionTheory.CosetSum
end

section

namespace GlobalTheory.CompanionTheory.LinAlg

open Module

theorem exists_common_eigenvector_in_submodule {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ι : Type} (H : ι → End ℂ W)
    (hc : ∀ i i', Commute (H i) (H i')) :
    ∀ (n : ℕ) (U : Submodule ℂ W), finrank ℂ U ≤ n → U ≠ ⊥ →
      (∀ i, ∀ x ∈ U, H i x ∈ U) →
      ∃ v ∈ U, v ≠ 0 ∧ ∃ χ : ι → ℂ, ∀ i, H i v = χ i • v := by
  intro n
  induction n with
  | zero =>
    intro U hU hne _
    exact absurd (Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)) hne
  | succ n ih =>
    intro U hU hne hinv
    by_cases hs : ∀ i, ∃ a : ℂ, ∀ x ∈ U, H i x = a • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      choose χ hχ using hs
      exact ⟨v, hv, hv0, χ, fun i => hχ i v hv⟩
    · push_neg at hs
      obtain ⟨i, hi⟩ := hs
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
      let R : End ℂ U := (H i).restrict (hinv i)
      obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue R
      obtain ⟨⟨w, hwU⟩, hw⟩ := ha.exists_hasEigenvector
      have hw' : H i w = a • w := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [R] using h1
      have hw0 : w ≠ 0 := by
        intro h
        exact hw.2 (Subtype.ext h)
      have hmem : ∀ {x : W}, x ∈ End.eigenspace (H i) a ↔ H i x = a • x := by
        intro x
        exact End.mem_eigenspace_iff
      have hU'ne : U ⊓ End.eigenspace (H i) a ≠ ⊥ := by
        intro h
        have : w ∈ U ⊓ End.eigenspace (H i) a := ⟨hwU, hmem.mpr hw'⟩
        rw [h] at this
        exact hw0 ((Submodule.mem_bot ℂ).mp this)
      have hlt : U ⊓ End.eigenspace (H i) a < U := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hx, hne'⟩ := hi a
        have : x ∈ U ⊓ End.eigenspace (H i) a := by rw [h]; exact hx
        exact hne' (hmem.mp this.2)
      have hfr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨v, hv, hv0, χ, hχ⟩ := ih (U ⊓ End.eigenspace (H i) a) (by omega) hU'ne (by
        intro k x hx
        refine ⟨hinv k x hx.1, hmem.mpr ?_⟩
        have h2 : H i x = a • x := hmem.mp hx.2
        have h3 : H i (H k x) = H k (H i x) := by
          have := congrArg (fun f : End ℂ W => f x) (hc i k).eq
          simpa using this
        rw [h3, h2, map_smul])
      exact ⟨v, hv.1, hv0, χ, hχ⟩

theorem exists_hasEigenvalue_ne_zero {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : End ℂ W) (v : W) (m : ℕ) (hm : finrank ℂ W ≤ m)
    (hv : (T ^ m) v ≠ 0) : ∃ μ : ℂ, μ ≠ 0 ∧ T.HasEigenvalue μ := by
  by_contra hno
  push_neg at hno
  have hbot : ∀ μ : ℂ, μ ≠ 0 → T.maxGenEigenspace μ = ⊥ := by
    intro μ hμ
    by_contra hne
    rw [End.maxGenEigenspace_eq_genEigenspace_finrank] at hne
    exact hno μ hμ (End.hasEigenvalue_of_hasGenEigenvalue (k := finrank ℂ W) hne)
  have htop : T.maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff, ← End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ = 0
    · rw [hμ]
    · rw [hbot μ hμ]
      exact bot_le
  have hvm : v ∈ T.maxGenEigenspace 0 := htop ▸ Submodule.mem_top
  rw [End.maxGenEigenspace_eq_genEigenspace_finrank, End.mem_genEigenspace_nat] at hvm
  simp only [zero_smul, sub_zero, LinearMap.mem_ker] at hvm
  apply hv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, pow_add, Module.End.mul_apply, hvm, map_zero]

theorem exists_joint_eigenvector_combination_ne_zero :
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J]
      (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) →
      ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m →
        ((∑ j, c j • H (s j)) ^ m) v ≠ 0 →
        ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  intro W _ _ _ ι J _ H hc c s v m hm hv
  obtain ⟨μ, hμ, hT⟩ := exists_hasEigenvalue_ne_zero _ v m hm hv
  have hcomm : ∀ i, Commute (∑ j, c j • H (s j)) (H i) := by
    intro i
    exact Commute.sum_left _ _ _ fun j _ => (hc (s j) i).smul_left (c j)
  obtain ⟨v₀, hv₀U, hv₀, χ, hχ⟩ := exists_common_eigenvector_in_submodule H hc _
    (End.eigenspace (∑ j, c j • H (s j)) μ) le_rfl hT (by
      intro i x hx
      rw [End.mem_eigenspace_iff] at hx ⊢
      have h3 : (∑ j, c j • H (s j)) (H i x) = H i ((∑ j, c j • H (s j)) x) := by
        have := congrArg (fun f : End ℂ W => f x) (hcomm i).eq
        simpa using this
      rw [h3, hx, map_smul])
  refine ⟨v₀, hv₀, χ, hχ, ?_⟩
  intro hsum
  have h1 : (∑ j, c j • H (s j)) v₀ = (∑ j, c j * χ (s j)) • v₀ := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hχ, Finset.sum_smul, mul_smul]
  rw [End.mem_eigenspace_iff, h1, hsum, zero_smul] at hv₀U
  exact hv₀ ((smul_eq_zero.mp hv₀U.symm).resolve_left hμ)

end GlobalTheory.CompanionTheory.LinAlg
end

section

namespace GlobalTheory.CompanionTheory.GroupIndex.RelProd

theorem relIndex_prod_eq_mul {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by
  have hmap : ((I₁.prod I₂).subgroupOf (K₁.prod K₂)) =
      ((I₁.subgroupOf K₁).prod (I₂.subgroupOf K₂)).comap
        (Subgroup.prodEquiv K₁ K₂).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_comap]
    exact Iff.rfl
  unfold Subgroup.relIndex
  rw [hmap, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv K₁ K₂).surjective,
    Subgroup.index_prod]

theorem relIndex_prod_ne_zero_of_ne_zero :
    ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂),
      I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  intro G₁ G₂ _ _ I₁ K₁ I₂ K₂ h₁ h₂
  rw [relIndex_prod_eq_mul]
  exact mul_ne_zero h₁ h₂

end GlobalTheory.CompanionTheory.GroupIndex.RelProd
end
