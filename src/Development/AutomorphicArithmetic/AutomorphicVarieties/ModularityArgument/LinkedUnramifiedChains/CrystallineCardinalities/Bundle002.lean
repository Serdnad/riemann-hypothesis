module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.homBd :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] (ε : D →* ℤ_[l]ˣ) (k : ℕ) (N : Type) [AddCommGroup N] (ρ : Representation ℤ D N) (e : Ok l O k ≃+ N) (χ : D → O) (s₀ : D), (l : O) ≠ 0 → (∀ s x, ρ s (e x) = e (χ s • x)) → χ s₀ - algebraMap ℤ_[l] O (ε s₀) ≠ 0 → (HomMu l k ε ρ).ncard ≤ Nat.card (O ⧸ Ideal.span {χ s₀ - algebraMap ℤ_[l] O (ε s₀)}) := by
  intro l _ O _ _ _ _ _ D _ ε k N _ ρ e χ s₀ hl hρ hc
  classical
  obtain ⟨hfinOk, hfinQ, hkill, -, -, hsm, -⟩ := okFin l O hl
  haveI : Finite (Ok l O k) := hfinOk k
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set c := χ s₀ - algebraMap ℤ_[l] O (ε s₀) with hcdef
  haveI : Finite (O ⧸ Ideal.span {c}) := hfinQ c hc
  let I' : Ideal (Ok l O k) := Ideal.span {algebraMap O (Ok l O k) c}
  let π := Ideal.Quotient.mk I'
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have kill : ∀ f ∈ HomMu l k ε ρ, ∀ a : Ok l O k, f (e (c • a)) = 0 := by
    intro f hf a
    have hf' : ∀ s x, f (ρ s x) = PadicInt.toZModPow k (ε s : ℤ_[l]) * f x := hf
    rw [hcdef, sub_smul, map_sub, map_sub, ← hρ, hf', hsm, map_nsmul, map_nsmul, nsmul_eq_mul,
      ZMod.natCast_zmod_val, sub_self]
  have wd : ∀ f ∈ HomMu l k ε ρ, ∀ y y' : Ok l O k, π y = π y' → f (e y) = f (e y') := by
    intro f hf y y' h
    have h' : y - y' ∈ I' := Ideal.Quotient.eq.mp h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h'
    have h2 : y - y' = c • a := by rw [← ha, Algebra.smul_def, mul_comm]
    have h3 := kill f hf a
    rw [← h2, map_sub, map_sub] at h3
    exact sub_eq_zero.mp h3
  let Φ : HomMu l k ε ρ → (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := fun f =>
    { toFun := fun q => f.1 (e (Function.surjInv hπ q))
      map_zero' := by
        rw [wd f.1 f.2 _ 0 (by rw [Function.surjInv_eq hπ, map_zero]), map_zero, map_zero]
      map_add' := by
        intro q q'
        rw [← map_add f.1, ← map_add e]
        apply wd f.1 f.2
        rw [map_add (f := _), Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ] }
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have h1 : ∀ y, f.1 (e y) = g.1 (e y) := by
      intro y
      have := congrArg (fun φ : Ok l O k ⧸ I' →+ ZMod (l ^ k) => φ (π y)) hfg
      change f.1 (e (Function.surjInv hπ (π y))) = g.1 (e (Function.surjInv hπ (π y))) at this
      rw [wd f.1 f.2 y _ (Function.surjInv_eq hπ _).symm, this,
        ← wd g.1 g.2 y _ (Function.surjInv_eq hπ _).symm]
    apply Subtype.ext
    ext x
    have := h1 (e.symm x)
    rwa [AddEquiv.apply_symm_apply] at this
  haveI : Finite (Ok l O k ⧸ I') := Finite.of_surjective π hπ
  have hQk : ∀ q : Ok l O k ⧸ I', l ^ k • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    rw [← map_nsmul, hkill, map_zero]
  obtain ⟨hfin2, hcard2⟩ := dualCard l k (Ok l O k ⧸ I') hQk
  let ψ : O ⧸ Ideal.span {c} →+* Ok l O k ⧸ I' :=
    Ideal.Quotient.lift (Ideal.span {c}) (π.comp (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [RingHom.comp_apply, map_mul, map_mul]
      have : π (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}) c) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rw [Set.mem_singleton_iff]; rfl))
      rw [this, mul_zero])
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := hπ q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  calc (HomMu l k ε ρ).ncard = Nat.card (HomMu l k ε ρ) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Ok l O k ⧸ I' →+ ZMod (l ^ k)) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (Ok l O k ⧸ I') := hcard2
    _ ≤ Nat.card (O ⧸ Ideal.span {c}) := Nat.card_le_card_of_surjective ψ hψ
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.AdjointKernelOpen

variable {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] {F : Frame l κ} {C : Type} [CommRing C]

private theorem r_ker_open (hdel : IsOpen (F.del.ker : Set F.Γ)) (B : Box F 3 C)
    (h : ∀ i j, IsLocallyConstant fun s => (B.r s).mat i j) : IsOpen (B.r.ker : Set F.Γ) := by
  have hset : (B.r.ker : Set F.Γ) = (F.del.ker : Set F.Γ) ∩
      ⋂ i, ⋂ j, (fun s => (B.r s).mat i j) ⁻¹' {(1 : Matrix (Fin 3) (Fin 3) C) i j} := by
    ext s
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [← B.nu s]
    constructor
    · intro hs
      refine ⟨by rw [hs]; rfl, fun i j => ?_⟩
      rw [hs]
      rfl
    · rintro ⟨h1, h2⟩
      apply SemidirectProduct.ext
      · apply Units.ext
        ext i j
        exact h2 i j
      · exact h1
  rw [hset]
  exact hdel.inter (isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun j => (h i j).isOpen_fiber _)

end UpperTheory.V.Z.J.AdjointKernelOpen

open UpperTheory.V.Z.J.AdjointKernelOpen in
theorem UpperTheory.V.Z.J.adOpen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (B : Box F 3 O) (k : ℕ), B.Cont (maximalIdeal O) → IsOpen ((adK B k).ker : Set F.Γ) := by
  intro l _ O _ _ _ _ _ F C₀ hF hl B k hB
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨N, hN⟩ := (okFin l O hl).2.2.2.2.1 k
  have hK : IsOpen ((boxK B k).r.ker : Set F.Γ) := by
    refine r_ker_open hF.del_open (boxK B k) fun i j => ?_
    have hc := (hB i j N).comp (Ideal.Quotient.factor hN)
    convert hc using 1
    funext s
    simp [Ideal.Quotient.factor_mk, boxK, Box.map, GG.map, GG.mat]
  refine Subgroup.isOpen_mono (fun s hs => ?_) hK
  rw [MonoidHom.mem_ker] at hs ⊢
  ext x
  simp [adK, Box.ad, adRep, hs]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem jtj {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) i j = X j.rev i.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.transpose_apply] <;> decide

private theorem count {A Q : Type} [AddCommGroup A] [AddCommGroup Q] [Finite Q] (S T : Set A) (H : AddSubgroup A)
    (hH : (H : Set A) = S) (hS : S.Finite) (hT : T ⊆ S) (f : A →+ Q) (hf : ∀ x ∈ S, f x = 0 → x ∈ T) :
    S.ncard ≤ T.ncard * Nat.card Q := by
  subst hH
  haveI : Finite H := hS.to_subtype
  have hTf : T.Finite := hS.subset hT
  haveI : Finite T := hTf.to_subtype
  let g : H →+ Q := f.comp H.subtype
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (H ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.range ≤ Nat.card Q :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have h4 : Nat.card g.ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, hf x.1.1 x.1.2 (AddMonoidHom.mem_ker.mp x.2)⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq T]
  change Nat.card H ≤ _
  rw [h1, h2, mul_comm]
  exact Nat.mul_le_mul h4 h3

private theorem core {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* GG (m := 3) (R := R)) (c g : Γ)
    (hc : c * c = 1) (hc1 : (r c).mat = 1) (hc2 : (r c).right = -1) (hg : (r g).right = 1)
    (z : Γ → Matrix (Fin 3) (Fin 3) R) (hz : ∀ s t, z (s * t) = z s + (r s).adFun (z t))
    (e : z c 0 0 = 0 ∧ z c 0 1 = 0 ∧ z c 1 0 = 0 ∧ z c 0 2 = 0 ∧ z c 2 0 = 0 ∧ z c 1 1 = 0)
    (e1 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 0 1 = 0)
    (e2 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 1 0 = 0) :
    z c = 0 ∧ ∀ i j, i ≠ j → (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j = 0 := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hleft : (r c).left = 1 := Units.ext hc1
  have ad1 : ∀ (x : GG (m := 3) (R := R)) X, x.right = 1 →
      x.adFun X = x.mat * X * ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro x X hx
    unfold GG.adFun
    rw [if_pos hx]
  have adc : ∀ X, (r c).adFun X = thetaLie X := by
    intro X
    unfold GG.adFun
    rw [if_neg (by rw [hc2]; exact hne), hc1, hleft, inv_one, Units.val_one, one_mul, mul_one]
  have ad0 : ∀ (x : GG (m := 3) (R := R)), x.adFun 0 = 0 := by
    intro x
    unfold GG.adFun thetaLie
    simp
  have z1 : z 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, ad1 _ _ (by simp)] at h
    simpa [GG.mat] using h
  have hsym : ∀ i j, z c i j = z c j.rev i.rev := by
    have h := hz c c
    rw [hc, z1, adc] at h
    intro i j
    have h2 : z c = Jmat R 3 * (z c)ᵀ * Jmat R 3 := by
      unfold thetaLie at h
      rw [eq_comm, add_neg_eq_zero] at h
      exact h
    have h3 := congrFun (congrFun h2 i) j
    rwa [jtj] at h3
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  have hzc : z c = 0 := by
    obtain ⟨e00, e01, e10, e02, e20, e11⟩ := e
    have s22 := hsym 2 2
    have s12 := hsym 1 2
    have s21 := hsym 2 1
    simp only [r1, r2] at s22 s12 s21
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> first | exact e00 | exact e01 | exact e10 | exact e02 | exact e20 | exact e11 | exact s22.trans e00 | exact s12.trans e01 | exact s21.trans e10
  refine ⟨hzc, ?_⟩
  set A : GL (Fin 3) R := (r g).left with hA
  have hgi : (r g⁻¹).right = 1 := by rw [map_inv, SemidirectProduct.inv_right, hg, inv_one]
  have hgil : (r g⁻¹).left = A⁻¹ := by
    rw [map_inv, SemidirectProduct.inv_left, hg, inv_one, map_one, MulAut.one_apply]
  have zgi : z g⁻¹ = -(((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * z g * (A : Matrix (Fin 3) (Fin 3) R)) := by
    have h := hz g⁻¹ g
    rw [inv_mul_cancel, z1, ad1 _ _ hgi, GG.mat, hgil, inv_inv] at h
    rw [eq_comm, ← eq_neg_iff_add_eq_zero] at h
    exact h
  have zh : z (c * g⁻¹ * c) = -(Jmat R 3 * (z g⁻¹)ᵀ * Jmat R 3) := by
    rw [hz, hzc, ad0, add_zero, hz, hzc, zero_add, adc]
    rfl
  have Mh : (r (c * g⁻¹ * c)).mat = Jmat R 3 * (A : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [GG.mat, map_mul, map_mul, SemidirectProduct.mul_left, hleft, map_one, mul_one,
      SemidirectProduct.mul_left, hleft, one_mul, hc2, hgil, map_inv, sgnAct_neg_one, theta_inv_val]
  have hD : z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat =
      z g * (A : Matrix (Fin 3) (Fin 3) R) - Jmat R 3 * (z g * (A : Matrix (Fin 3) (Fin 3) R))ᵀ * Jmat R 3 := by
    rw [zh, Mh, zgi]
    have hJ := Jmat_mul_Jmat (R := R) 3
    have hAA : ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * (A : Matrix (Fin 3) (Fin 3) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    simp only [Matrix.transpose_neg, Matrix.transpose_mul, neg_neg, Matrix.mul_neg, Matrix.neg_mul, GG.mat,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Jmat R 3) (Jmat R 3), hJ, Matrix.one_mul,
      ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ (A : Matrix (Fin 3) (Fin 3) R)ᵀ,
      hAA, Matrix.one_mul]
  have hDe : ∀ i j, (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j =
      (z g * (A : Matrix (Fin 3) (Fin 3) R)) i j - (z g * (A : Matrix (Fin 3) (Fin 3) R)) j.rev i.rev := by
    intro i j
    rw [hD, Matrix.sub_apply, jtj]
  intro i j hij
  rw [hDe] at e1 e2 ⊢
  rw [r0, r1] at e1 e2
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact sub_self _ | exact e1 | exact e2 | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 2 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 0 1 = 0 by linear_combination -e1) | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 2 1 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 0 = 0 by linear_combination -e2)

private def zlGrp {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] (F : Frame l κ) {N : Type} [AddCommGroup N]
    (ρ : Representation ℤ F.Γ N) (Z : ∀ v, AddSubgroup (F.Gv v → N)) : AddSubgroup (F.Γ → N) where
  carrier := ZL F ρ fun v => Z v
  add_mem' := by
    rintro x y ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
    refine ⟨⟨a1.add b1, fun s t => ?_⟩, fun v => (Z v).add_mem (a3 v) (b3 v)⟩
    simp only [Pi.add_apply, a2, b2, map_add (f := _)]; abel
  zero_mem' := ⟨⟨IsLocallyConstant.const 0, by simp⟩, fun v => (Z v).zero_mem⟩
  neg_mem' := by
    rintro x ⟨⟨a1, a2⟩, a3⟩
    refine ⟨⟨a1.neg, fun s t => ?_⟩, fun v => (Z v).neg_mem (a3 v)⟩
    simp only [Pi.neg_apply, a2, map_neg]; abel

private def ent {R Γ : Type} [CommRing R] (c g h : Γ) (P Q : Matrix (Fin 3) (Fin 3) R) :
    (Γ → Matrix (Fin 3) (Fin 3) R) →+ (Fin 8 → R) :=
  AddMonoidHom.mk' (fun z => ![z c 0 0, z c 0 1, z c 1 0, z c 0 2, z c 2 0, z c 1 1,
    (z g * P - z h * Q) 0 1, (z g * P - z h * Q) 1 0]) fun x y => by
      have e : (x + y) g * P - (x + y) h * Q = (x g * P - x h * Q) + (y g * P - y h * Q) := by
        simp only [Pi.add_apply, Matrix.add_mul]; abel
      rw [e]
      ext i
      fin_cases i <;> rfl

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.normCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → (∀ v, ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v) → (ZL F (adK B k) (Zv B k)).Finite → (ZL F (adK B k) (Zv B k)).ncard ≤ (ZN B k).ncard * Nat.card (Ok l O k) ^ 8 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B _ hB _ k _ hZ hfin
  haveI : Finite (Ok l O k) := (okFin l O hl).1 k
  choose Z hZ using hZ
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hs : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c := by
    simp [Frame.star, Frame.conj, hc, mul_assoc]
  have h := count (ZL F (adK B k) (Zv B k)) (ZN B k) (zlGrp F (adK B k) Z)
    (congrArg (ZL F (adK B k)) (funext hZ)) hfin (fun z hz => hz.1)
    (ent F.c F.g0 (F.star F.g0) ((boxK B k).r F.g0).mat ((boxK B k).r (F.star F.g0)).mat) (fun z hz h0 => by
      refine ⟨hz, ?_⟩
      have e6 := congrFun h0 6
      have e7 := congrFun h0 7
      rw [hs] at e6 e7 ⊢
      have hatc : ((boxK B k).r F.c).mat = 1 := by
        let q : O →+* Ok l O k := Ideal.Quotient.mk _
        change q.mapMatrix (B.r F.c).mat = 1
        rw [hB.atc, map_one]
      exact core (boxK B k).r F.c F.g0 hF.c_sq hatc (((boxK B k).nu _).trans hF.del_c)
        (((boxK B k).nu _).trans F.g0.2) z hz.1.2
        ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2, congrFun h0 3, congrFun h0 4, congrFun h0 5⟩ e6 e7)
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
end
