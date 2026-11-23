module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

private theorem arch_gen {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R)) (y : GG (m := 3) (R := R))
    (hy : y * y = 1) (hr : y.right = -1) :
    {X : Matrix (Fin 3) (Fin 3) R | GG.ad (m := 3) (R := R) y X = X}.ncard ≤ Nat.card R ^ 3 := by
  obtain ⟨a, s⟩ := y
  obtain rfl : s = -1 := hr
  have h : ((-1 : ℤˣ) = 1) = False := by decide
  have h1 : a * theta a = 1 := by
    have := congrArg SemidirectProduct.left hy
    simpa [SemidirectProduct.mul_left] using this
  have h3 : theta a = a⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h4 : (a : Matrix (Fin 3) (Fin 3) R) = Jmat R 3 * (a : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [← theta_inv_val, h3, inv_inv]
  have hJ := Jmat_mul_Jmat (R := R) 3
  set A : Matrix (Fin 3) (Fin 3) R := a.val with hA
  set A' : Matrix (Fin 3) (Fin 3) R := (a⁻¹ : GL (Fin 3) R).val with hA'
  have hAA : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB : (A * Jmat R 3)ᵀ = A * Jmat R 3 := by
    rw [Matrix.transpose_mul, Jmat_transpose]
    conv_rhs => rw [h4, Matrix.mul_assoc, hJ, Matrix.mul_one]
  have key : ∀ X : Matrix (Fin 3) (Fin 3) R, GG.ad (m := 3) (R := R) ⟨a, -1⟩ X = X →
      (X * (A * Jmat R 3))ᵀ = -(X * (A * Jmat R 3)) := by
    intro X hX
    have hX' : A * (-(Jmat R 3 * Xᵀ * Jmat R 3)) * A' = X := by
      simpa only [GG.ad_apply, GG.adFun, GG.mat, h, if_false, thetaLie] using hX
    rw [Matrix.transpose_mul, hB]
    conv_rhs => rw [← hX']
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A' A, hAA, Matrix.one_mul, hJ, Matrix.mul_one]
  have anti : ∀ Y : Matrix (Fin 3) (Fin 3) R, Yᵀ = -Y → Y 0 1 = 0 → Y 0 2 = 0 → Y 1 2 = 0 → Y = 0 := by
    intro Y hY e1 e2 e3
    have hs : ∀ i j, Y j i = -Y i j := fun i j => congrFun (congrFun hY i) j
    have hd : ∀ i, Y i i = 0 := fun i => by
      apply h2.mul_left_cancel
      have := hs i i
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, e1, e2, e3, hs 0 1, hs 0 2, hs 1 2]
  let f : Matrix (Fin 3) (Fin 3) R → R × R × R := fun X =>
    ((X * (A * Jmat R 3)) 0 1, (X * (A * Jmat R 3)) 0 2, (X * (A * Jmat R 3)) 1 2)
  have hinj : Set.InjOn f {X : Matrix (Fin 3) (Fin 3) R | GG.ad (m := 3) (R := R) ⟨a, -1⟩ X = X} := by
    intro X hX X' hX' hf
    simp only [f, Prod.mk.injEq] at hf
    have h0 : X * (A * Jmat R 3) - X' * (A * Jmat R 3) = 0 := by
      apply anti
      · rw [Matrix.transpose_sub, key X hX, key X' hX']; abel
      · rw [Matrix.sub_apply, hf.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.1, sub_self]
      · rw [Matrix.sub_apply, hf.2.2, sub_self]
    have h5 := congrArg (· * (Jmat R 3 * A')) (sub_eq_zero.1 h0)
    simp only [Matrix.mul_assoc] at h5
    rwa [← Matrix.mul_assoc (Jmat R 3), hJ, Matrix.one_mul, hAA', Matrix.mul_one, Matrix.mul_one] at h5
  calc _ ≤ (Set.univ : Set (R × R × R)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun _ _ => Set.mem_univ _) hinj (Set.toFinite _)
    _ = Nat.card R ^ 3 := by rw [Set.ncard_univ, Nat.card_prod, Nat.card_prod]; ring

theorem UpperTheory.V.Z.J.archUp :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → l ≠ 2 →
    ∀ (x : GG (m := 3) (R := O)), x * x = 1 → x.right = -1 → ∀ k, 0 < k →
    {X : Matrix (Fin 3) (Fin 3) (Ok l O k) |
      GG.ad (m := 3) (R := Ok l O k) (GG.map (Ideal.Quotient.mk _) x) X = X}.ncard ≤
    Nat.card (Ok l O k) ^ 3 := by
  intro l hl O _ _ _ _ _ hl0 hl2 x hx hr k _
  have hfin : Finite (Ok l O k) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hne : Ideal.span {(l : O) ^ k} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hl0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    haveI : Finite (O ⧸ maximalIdeal O) := (inferInstance : Finite (ResidueField O))
    have hf : Finite (O ⧸ maximalIdeal O ^ n) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at hf
    exact hf
  have h2 : IsUnit (2 : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h
    have h' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')
  have h2' : IsUnit (2 : Ok l O k) := by
    simpa only [map_ofNat] using h2.map (Ideal.Quotient.mk (Ideal.span {(l : O) ^ k}))
  exact arch_gen h2' _ (by rw [← map_mul, hx, map_one]) hr
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add (f := _)]; abel⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem card_ZcA {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    Nat.card (ZcA ρ) = (Zc ρ).ncard := Nat.card_coe_set_eq (Zc ρ)

private theorem idx_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    f.range.index * Nat.card A = Nat.card B * Nat.card f.ker := by
  rw [← AddSubgroup.index_mul_card f.range, ← AddSubgroup.index_mul_card f.ker, AddSubgroup.index_ker]
  ring

private def ZcQ {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) : ZcA ρ →+ ZcA (ρ.quotient N' h) where
  toFun z := ⟨fun s => N'.mkQ (z.1 s), z.2.1.comp N'.mkQ, fun s t => by
    show N'.mkQ (z.1 (s * t)) = N'.mkQ (z.1 s + ρ s (z.1 t))
    rw [z.2.2 s t]⟩
  map_zero' := by ext s; rfl
  map_add' a b := by ext s; rfl

private theorem ker_le {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N)
    (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (hf : (Zc (ρ.subrepresentation N' h)).Finite) :
    Nat.card (ZcQ ρ N' h).ker ≤ (Zc (ρ.subrepresentation N' h)).ncard := by
  have hm : ∀ z : (ZcQ ρ N' h).ker, ∀ s, z.1.1 s ∈ N' := fun z s => by
    have h1 : ZcQ ρ N' h z.1 = 0 := z.2
    have h2 : N'.mkQ (z.1.1 s) = 0 := congrFun (congrArg Subtype.val h1) s
    exact (Submodule.Quotient.mk_eq_zero N').1 h2
  haveI : Finite (Zc (ρ.subrepresentation N' h)) := hf
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun z => ⟨fun s => ⟨z.1.1 s, hm z s⟩,
    IsLocallyConstant.desc _ (Subtype.val) z.1.2.1 Subtype.val_injective, fun s t => Subtype.ext (z.1.2.2 s t)⟩) ?_
  intro a b hab
  ext s
  exact congrArg Subtype.val (congrFun (congrArg Subtype.val hab) s)

private theorem homMu_le {D N : Type} [Group D] [AddCommGroup N] [Finite N] (l : ℕ) [Fact l.Prime] (k : ℕ) (ε : D →* ℤ_[l]ˣ)
    (ρ : Representation ℤ D N) (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) :
    (HomMu l k ε (ρ.quotient N' h)).ncard ≤ (HomMu l k ε ρ).ncard ∧ 0 < (HomMu l k ε ρ).ncard := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (N →+ ZMod (l ^ k)) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Set.ncard_le_ncard_of_injOn (fun f => f.comp N'.mkQ.toAddMonoidHom) (fun f hf s x => hf s (N'.mkQ x)) ?_, ?_⟩
  · intro a _ b _ hab
    ext x
    obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
    exact DFunLike.congr_fun hab y
  · exact (Set.ncard_pos).2 ⟨0, fun s x => by simp⟩

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.lift :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d k : ℕ), 0 < k → LE l D ε d → ∀ (N : Type) [AddCommGroup N] [Finite N] (ρ : Representation ℤ D N), (∀ x : N, l ^ k • x = 0) → IsOpen (ρ.ker : Set D) → ∀ (N' : Submodule ℤ N) (h : ∀ s, N' ≤ N'.comap (ρ s)) (C : ℕ), (HomMu l k ε (ρ.subrepresentation N' h)).ncard ≤ C → ∀ z : D → N, IsLocallyConstant z → (∀ s s', z (s * s') - z s - ρ s (z s') ∈ N') → ∃ y ∈ Zc ρ, ∀ s, y s - C.factorial • z s ∈ N' := by
  intro l _ D _ _ _ ε d k hk hLE N _ _ ρ hN hρ N' h C hC z hz hz'
  haveI : Finite (N ⧸ N') := Finite.of_surjective _ N'.mkQ_surjective
  obtain ⟨-, e1⟩ := hLE k hk N ρ hN hρ
  obtain ⟨f2, e2⟩ := hLE k hk N' (ρ.subrepresentation N' h) (fun x => Subtype.ext (hN x.1))
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ρ s x.1 = x.1
      rw [h1]; rfl) hρ)
  obtain ⟨f3, e3⟩ := hLE k hk (N ⧸ N') (ρ.quotient N' h) (fun x => by
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      rw [← map_nsmul, hN, map_zero])
    (Subgroup.isOpen_mono (H₁ := ρ.ker) (fun s hs => by
      have h1 : ρ s = 1 := hs
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := N'.mkQ_surjective x
      show N'.mkQ (ρ s y) = N'.mkQ y
      rw [h1]; rfl) hρ)
  have e4 := idx_mul (ZcQ ρ N' h)
  rw [card_ZcA, card_ZcA, e1, e3] at e4
  have e5 := ker_le ρ N' h f2
  rw [e2] at e5
  obtain ⟨e6, e7⟩ := homMu_le l k ε ρ N' h
  have e8 : Nat.card N = Nat.card N' * Nat.card (N ⧸ N') := Submodule.card_eq_card_quotient_mul_card N'
  have hpos : 0 < Nat.card N ^ (1 + d) * (HomMu l k ε ρ).ncard := Nat.mul_pos (pow_pos Nat.card_pos _) e7
  have hle : (ZcQ ρ N' h).range.index ≤ C := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e4]
    calc _ ≤ Nat.card (N ⧸ N') ^ (1 + d) * (HomMu l k ε ρ).ncard * (Nat.card N' ^ (1 + d) * C) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e6) (e5.trans (Nat.mul_le_mul_left _ hC))
      _ = _ := by rw [e8, mul_pow]; ring
  haveI : Finite (ZcA (ρ.quotient N' h)) := f3
  have hne : (ZcQ ρ N' h).range.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hle
  let w : ZcA (ρ.quotient N' h) := ⟨fun s => N'.mkQ (z s), hz.comp N'.mkQ, fun s t => by
    show N'.mkQ (z (s * t)) = N'.mkQ (z s + ρ s (z t))
    refine (Submodule.Quotient.eq N').2 ?_
    rw [← sub_sub]; exact hz' s t⟩
  have hw : C.factorial • w ∈ (ZcQ ρ N' h).range := by
    rw [hc, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_index_mem _ w) c
  obtain ⟨y, hy⟩ := hw
  refine ⟨y.1, y.2, fun s => (Submodule.Quotient.eq N').1 ?_⟩
  have h2 : N'.mkQ (y.1 s) = C.factorial • N'.mkQ (z s) := congrFun (congrArg Subtype.val hy) s
  rw [← map_nsmul] at h2
  exact h2
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.wtCut :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D) (d k m : ℕ) (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N], GenI l I d → (∀ x : A, l ^ k • x = 0) → ∀ (Z : AddSubgroup (D → N)), Finite Z → ∀ p : Fin m → N →+ A, (∀ z ∈ Z, IsLocallyConstant z ∧ ∀ j s s', p j (z (s * s')) = p j (z s) + p j (z s')) → Nat.card Z ≤ {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard * Nat.card A ^ (m * d) := by
  intro l _ D _ _ I d k m A N _ _ _ hG hA Z _ p hZ
  obtain ⟨u, -, hu⟩ := hG
  let Φ : Z →+ (Fin m → Fin d → A) :=
    { toFun := fun z j a => p j (z.1 (u a))
      map_zero' := by
        funext j a
        simp
      map_add' := by
        intro x y
        funext j a
        simp }
  let S : Set (D → N) := {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}
  have hSfin : S.Finite := Set.Finite.subset (Set.toFinite (Z : Set (D → N))) (fun z hz => hz.1)
  have hker : ∀ z ∈ Φ.ker, (z : D → N) ∈ S := by
    intro z hz
    refine ⟨z.2, fun j s hs => ?_⟩
    have hz0 : ∀ a, p j (z.1 (u a)) = 0 := fun a => congrFun (congrFun hz j) a
    exact hu k A hA (fun s => p j (z.1 s)) ((hZ _ z.2).1.comp (p j))
      (fun s t => (hZ _ z.2).2 j s t) hz0 s hs
  have h1 : Nat.card Φ.ker ≤ S.ncard := by
    rw [← Nat.card_coe_set_eq]
    haveI := hSfin.to_subtype
    refine Nat.card_le_card_of_injective (fun z : Φ.ker => (⟨z.1.1, hker z.1 z.2⟩ : S)) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  have h2 : Nat.card Φ.range ≤ Nat.card A ^ (m * d) := by
    calc Nat.card Φ.range ≤ Nat.card (Fin m → Fin d → A) :=
          Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Nat.card A ^ (m * d) := by
          simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
  calc Nat.card Z = Nat.card Φ.ker * Φ.ker.index := (AddSubgroup.card_mul_index _).symm
    _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [AddSubgroup.index_ker]
    _ ≤ S.ncard * Nat.card A ^ (m * d) := Nat.mul_le_mul h1 h2
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.leTrans :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (e : D ≃ₜ* D') (ε : D' →* ℤ_[l]ˣ) (d : ℕ), LE l D' ε d → LE l D (ε.comp (e : D →* D')) d := by
  intro l _ D D' _ _ _ _ e ε d h k hk N _ _ ρ hN hker
  let ρ' : Representation ℤ D' N := ρ.comp (e.symm : D' →* D)
  have hρ' : ∀ s : D', ρ' s = ρ (e.symm s) := fun s => rfl
  have hker' : IsOpen (↑(MonoidHom.ker ρ') : Set D') := by
    have hset : (↑(MonoidHom.ker ρ') : Set D') = e.symm ⁻¹' (↑(MonoidHom.ker ρ) : Set D) := by
      ext s
      simp [hρ']
    rw [hset]
    exact hker.preimage (map_continuous e.symm)
  obtain ⟨hfin, hcard⟩ := h k hk N ρ' hN hker'
  have himg : Zc ρ = (fun z : D' → N => z ∘ e) '' Zc ρ' := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z ∘ e.symm, ⟨hz1.comp_continuous (map_continuous e.symm), ?_⟩, ?_⟩
      · intro s t
        simp only [Function.comp_apply, map_mul, hρ']
        exact hz2 _ _
      · funext s
        simp
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨hw1.comp_continuous (map_continuous e), ?_⟩
      intro s t
      simp only [Function.comp_apply, map_mul]
      rw [hw2, hρ']
      simp
  have hinj : Function.Injective (fun z : D' → N => z ∘ e) := by
    intro z₁ z₂ hz
    funext s
    have := congrFun hz (e.symm s)
    simpa using this
  have hmu : HomMu l k (ε.comp (e : D →* D')) ρ = HomMu l k ε ρ' := by
    ext f
    simp only [HomMu, Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro hf s x
      rw [hρ']
      have := hf (e.symm s) x
      simpa using this
    · intro hf s x
      have := hf (e s) x
      rw [hρ'] at this
      simpa using this
  rw [himg, hmu]
  exact ⟨hfin.image _, by rw [Set.ncard_image_of_injective _ hinj]; exact hcard⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem ac_const {D R : Type} [TopologicalSpace D] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : D => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := fun N => by
  have h := (hf N).add (hg N)
  convert h using 1
  funext s
  exact map_add (Ideal.Quotient.mk (I ^ N)) (f s) (g s)

private theorem ac_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f g : D → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  have h := (hf N).mul (hg N)
  convert h using 1
  funext s
  exact map_mul (Ideal.Quotient.mk (I ^ N)) (f s) (g s)

private theorem ac_comp {D E R : Type} [TopologicalSpace D] [TopologicalSpace E] [CommRing R] {I : Ideal R}
    {f : E → R} (hf : AdicCont I f) {φ : D → E} (hφ : Continuous φ) : AdicCont I fun s => f (φ s) :=
  fun N => (hf N).comp_continuous hφ

private theorem adic_continuous_sum_three {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f : Fin 3 → D → R}
    (hf : ∀ a, AdicCont I (f a)) : AdicCont I fun s => ∑ a, f a s := by
  simp only [Fin.sum_univ_three]
  exact ac_add (ac_add (hf 0) (hf 1)) (hf 2)

variable {l : ℕ} [Fact l.Prime]

private theorem triOf_val {C : Type} [CommRing C] {κ : Type} [Field κ] {F : Frame l κ} (B : Box F 3 C) (v : F.V)
    (s : F.Gv v) : (triOf B v s : Matrix (Fin 3) (Fin 3) C) =
      (B.g v : Matrix (Fin 3) (Fin 3) C) * (B.r (F.loc v s)).mat *
        (((B.g v)⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := rfl

private theorem pow_w_ne {κ : Type} [Field κ] (x : κˣ) (hx : x ^ 2 ≠ 1) (i j : Fin 3) (h : i ≠ j) :
    ((x ^ w 3 i : κˣ) : κ) ≠ ((x ^ w 3 j : κˣ) : κ) := by
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have h1 : x ≠ 1 := fun e => hx (by simp [e])
  have h2 : x ≠ x⁻¹ := fun e => hx (by
    rw [pow_two]
    nth_rewrite 2 [e]
    simp)
  have h3 : x⁻¹ ≠ 1 := fun e => h1 (by simpa using e)
  intro e
  have e' := Units.ext e
  fin_cases i <;> fin_cases j <;> simp_all

private theorem genI_of {D : Type} [Group D] [TopologicalSpace D] {I : Subgroup D} {d : ℕ}
    (h : ∃ u : Fin d → D, (∀ a, u a ∈ I) ∧ ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : D →* A,
      IsOpen (χ.ker : Set D) → (∀ a, χ (u a) = 1) → ∀ g ∈ I, χ g = 1) : GenI l I d := by
  obtain ⟨u, hu, hχ⟩ := h
  refine ⟨u, hu, ?_⟩
  intro k A _ _ hk a hloc hadd hz g hg
  have h1 : a 1 = 0 := by simpa using hadd 1 1
  let χ : D →* Multiplicative A :=
    { toFun := fun s => Multiplicative.ofAdd (a s)
      map_one' := by rw [h1]; rfl
      map_mul' := fun s t => by rw [hadd]; rfl }
  have hp : IsPGroup l (Multiplicative A) := fun x => ⟨k, by
    show Multiplicative.ofAdd (l ^ k • Multiplicative.toAdd x) = 1
    rw [hk]
    rfl⟩
  have ho : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = a ⁻¹' {0} := by
      ext s
      show χ s = 1 ↔ a s = 0
      exact Iff.rfl
    rw [this]
    exact hloc.isOpen_fiber 0
  exact hχ (Multiplicative A) hp χ ho (fun j => by
    show Multiplicative.ofAdd (a (u j)) = 1
    rw [hz]
    rfl) g hg

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.triOk :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ v, TriRep (triOf B v) ∧ GenI l (F.Iv v) (F.dv v) ∧ ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
  intro l _ O _ _ _ _ _ F C₀ hF _ ρ B hL hB hC v
  have hd : ∀ s j, (triOf B v s : Matrix (Fin 3) (Fin 3) O) j j = (ρ.ψ v j s : O) := by
    intro s j
    rw [triOf_val]
    have e : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hB.res (F.loc0 v s)
    rw [e]
    exact hB.psi v j s
  have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
  refine ⟨⟨fun i j => ?_, fun s => ?_, ?_⟩, ?_, hd⟩
  · have e : (fun s => (triOf B v s : Matrix (Fin 3) (Fin 3) O) i j) = fun s =>
        ∑ b, (∑ a, (B.g v : Matrix (Fin 3) (Fin 3) O) i a * (B.r (F.loc v s)).mat a b) *
          (((B.g v)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) b j := by
      funext s
      rw [triOf_val, Matrix.mul_apply]
      simp only [Matrix.mul_apply]
    rw [e]
    exact adic_continuous_sum_three fun b => ac_mul (adic_continuous_sum_three fun a => ac_mul (ac_const _ _) (ac_comp (hC a b) hloc)) (ac_const _ _)
  · exact B.tri v s
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij => ?_⟩
    rw [hd, hd]
    by_contra hn
    have hm : (ρ.ψ v i s : O) - (ρ.ψ v j s : O) ∈ maximalIdeal O := hn
    have h0 := (res_eq_zero_iff O O _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    have hi := hL.2.1.2 v i s
    have hj := hL.2.1.2 v j s
    simp only [NRep.map_ψ, RingHom.id_apply] at hi hj
    exact pow_w_ne _ hs i j hij (by rw [← hi, ← hj]; exact h0)
  · obtain ⟨u, a₀, hu, -, hχ⟩ := hF.gen v
    exact genI_of ⟨u, fun a => (hu a).1, hχ⟩
end
