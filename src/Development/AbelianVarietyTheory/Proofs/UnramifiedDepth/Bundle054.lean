module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle049
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle030
import Formalism.LocalToGlobal.CharacterGerms.Bundle006
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem td_mem {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (x : κ → C) :
    x ∈ (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a)) ↔
      ∀ a, ρ a *ᵥ x = τ a • x := by
  simp [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

private theorem td_reindex {C OE κ κ' : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ' ≃ κ) (ρ : OE → Matrix κ κ C) (τ : OE →+* C) :
    eigDim C (fun a => (ρ a).submatrix e e) τ = eigDim C ρ τ := by
  unfold eigDim
  rw [← LinearEquiv.finrank_map_eq (LinearEquiv.funCongrLeft C C e)
    (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a))]
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [Submodule.mem_map_equiv, td_mem (fun a => (ρ a).submatrix e e), td_mem ρ]
  refine forall_congr' fun a => ?_
  rw [Matrix.submatrix_mulVec_equiv]
  have hx : (LinearEquiv.funCongrLeft C C e).symm x = x ∘ e.symm := by
    ext i; simp
  rw [hx]
  constructor
  · intro h
    ext i
    have := congrFun h (e.symm i)
    simpa using this
  · intro h
    ext i
    have := congrFun h (e i)
    simpa using this

private theorem td_base {C O OE κ : Type} [Field C] [CommRing O] [Algebra O C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ O) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C (fun a => (ρ a).map (algebraMap O C)) τ := by
  rfl

private theorem td_twist {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (s : OE →+* OE) (hs : ∀ a, s (s a) = a) :
    eigDim C (fun a => ρ (s a)) τ = eigDim C ρ (τ.comp s) := by
  unfold eigDim
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [td_mem (fun a => ρ (s a)), td_mem ρ]
  constructor
  · intro h a
    have := h (s a)
    rw [hs] at this
    simpa using this
  · intro h a
    have := h (s a)
    simpa [hs] using this

private theorem td_field {C OE : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] {g : ℕ}
    (ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C) (L : OE →+* Matrix (Fin g) (Fin g) C)
    (s : OE →+* OE) (hs : ∀ a, s (s a) = a) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C)
    (hE : IsUnit E.det) (hinv : ∀ a, (ρ a)ᵀ * E = E * ρ (s a))
    (H B : Matrix (Fin g) (Fin g ⊕ Fin g) C) (hH : ∀ a, H * ρ a = (L (s a))ᵀ * H) (c : C) (hc : c ≠ 0)
    (hform : Bᵀ * H - Hᵀ * B = c • E) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C L τ + eigDim C L (τ.comp s) := by
  set A : Matrix (Fin g ⊕ Fin g) (Fin g) C := E⁻¹ * Hᵀ with hA
  set A' : Matrix (Fin g) (Fin g ⊕ Fin g) C := (-c⁻¹) • B with hA'
  set B' : Matrix (Fin g ⊕ Fin g) (Fin g) C := c⁻¹ • (E⁻¹ * Bᵀ) with hB'
  have h1 : A * A' + B' * H = 1 := by
    have : A * A' + B' * H = c⁻¹ • (E⁻¹ * (Bᵀ * H - Hᵀ * B)) := by
      simp only [hA, hA', hB', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_sub, smul_sub,
        neg_smul, Matrix.mul_neg]
      abel
    rw [this, hform, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hE, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : Matrix.fromRows A' H * Matrix.fromCols A B' = 1 := by
    rw [← Matrix.fromCols_mul_fromRows_eq_one_comm (Equiv.refl _), Matrix.fromCols_mul_fromRows, h1]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  obtain ⟨h21, -, h23, h24⟩ := h2
  have hρA : ∀ a, ρ a * A = A * L a := by
    intro a
    have e1 : ρ a * E⁻¹ = E⁻¹ * (ρ (s a))ᵀ := by
      have := hinv (s a)
      rw [hs] at this
      calc ρ a * E⁻¹ = E⁻¹ * (E * ρ a) * E⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE, Matrix.one_mul]
        _ = E⁻¹ * (ρ (s a))ᵀ * (E * E⁻¹) := by rw [← this]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
    have e2 := congrArg Matrix.transpose (hH (s a))
    rw [hs, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e2
    rw [hA, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2, Matrix.mul_assoc]
  let e : Fin (g + g) ≃ Fin g ⊕ Fin g := finSumFinEquiv.symm
  let ρ' : OE →+* Matrix (Fin (g + g)) (Fin (g + g)) C :=
    (Matrix.reindexAlgEquiv C C e.symm).toRingEquiv.toRingHom.comp ρ
  have hρ' : ∀ a, ρ' a = (ρ a).submatrix e e := fun a => rfl
  let LT : OE →+* Matrix (Fin g) (Fin g) C :=
    { toFun := fun a => (L (s a))ᵀ
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_comm a b, map_mul, map_mul, Matrix.transpose_mul]
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hsp : SplitEx (A.submatrix e id) (H.submatrix id e) := by
    refine ⟨?_, A'.submatrix id e, B'.submatrix e id, ?_, ?_, ?_⟩
    · rw [Matrix.submatrix_mul_equiv, h23]; simp
    · rw [Matrix.submatrix_mul_equiv, h21]; simp
    · rw [Matrix.submatrix_mul_equiv, h24]; simp
    · rw [← Matrix.submatrix_one_equiv e, ← h1]
      ext i j
      simp [Matrix.mul_apply]
  have k1 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE (g + g) g g _ _ hsp ρ' L LT
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hH]
      ext i j
      simp [Matrix.mul_apply, LT])
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hρA]
      ext i j
      simp [Matrix.mul_apply]) τ).1
  let Z : OE →+* Matrix (Fin 0) (Fin 0) C :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }
  have k2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE g g 0 _ _ (splitEx_one g) (L.comp s) (L.comp s) Z
    (fun a => Subsingleton.elim _ _) (fun a => by simp) τ).2
  have k3 : eigDim C ρ' τ = eigDim C ρ τ := td_reindex e ρ τ
  have k4 : eigDim C LT τ = eigDim C L (τ.comp s) := k2.trans (td_twist L τ s hs)
  rw [← k3, k1, k4]

theorem eigDim_tate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H τ
  let j : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let f : ℤ_[p] →+* C := (algebraMap O C).comp (algebraMap ℤ_[p] O)
  let s : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hs : ∀ a, s (s a) = a := fun a => star_star a
  have hj : ∀ a, sigE p OE (j a) = j (s a) := fun a => rfl
  let ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C := (f.mapMatrix.comp H.ρ.toRingHom).comp j
  let L : OE →+* Matrix (Fin g) (Fin g) C := ((algebraMap O C).mapMatrix.comp H.ρL).comp j
  have hρ : ∀ a, ρ a = (H.ρ (j a)).map f := fun a => rfl
  have hL : ∀ a, L a = (H.ρL (j a)).map (algebraMap O C) := fun a => rfl
  have hc : algebraMap O C cp ≠ 0 := by
    intro h
    have h1 := hU.cp_val
    have h2 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h, map_zero, zero_pow h2] at h1
    exact hU.p_ne h1.symm
  have key := td_field ρ L s hs (H.E.map f)
    (by
      have := H.isUnit_det_E.map f
      rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this)
    (fun a => by
      rw [hρ, hρ, ← hj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant])
    (H.Ht.map (algebraMap O C)) (H.Bt.map (algebraMap O C))
    (fun a => by
      have := congrArg (fun M => M.map (algebraMap O C)) (H.Ht_equivariant.1 (j a))
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      rw [hρ, hL, ← hj, ← this]
      rfl)
    (algebraMap O C cp) hc
    (by
      have := congrArg (fun M => M.map (algebraMap O C)) H.form_eq_alt
      simp only [Matrix.map_sub _ (map_sub (algebraMap O C)), Matrix.map_mul, Matrix.transpose_map] at this
      rw [this]
      ext i k
      simp [f]) τ
  rw [td_base, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a))]
  exact key

end GlobalTheory.ChF
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

private theorem ge_coeff_rename_inl {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι →₀ ℕ, ν.degree = ∑ c, μ (Sum.inl c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inl F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]

private theorem ge_coeff_rename_inr {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι' C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι' →₀ ℕ, ν.degree = ∑ c, μ (Sum.inr c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inr F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective]

private theorem constantCoeff_linPull_eq_zero {C : Type} [Field C] {σ ι : Type} [Fintype σ]
    [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (h : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  unfold linPull
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  · intro x
    simp
  · exact h

private theorem pderiv_inr_mainM_one {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (mainM V 1 Φ) =
      MvPowerSeries.rename Sum.inl ((V.l : C)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X c : MvPowerSeries ι C) ^ V.l) := by
  have hE : expE V.l 1 = 1 := by simp [expE]
  unfold mainM
  rw [hE, pow_one, pow_one]

  simp only [map_smul, map_sum, MvPowerSeries.rename_X, map_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Derivation.map_smul, Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr]
    simp [mul_comm]
  · intro x _ hx
    rw [Derivation.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr,
      MvPowerSeries.pderiv_X_of_ne (fun h => hx (Sum.inr_injective h))]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem mPlus_of_good_tangents : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  intro C _ V d _ I J _ _ X hAlt hd g a S t hT N em v' hty hal hint hpure μ hμl hμr
  by_cases h0 : ∀ b, μ (Sum.inr b) = 0
  · rw [GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis _ _ _ _ _ X g a 1 _ _ _ v' _ μ h0]
    exact VF.Ge.zero 0
  simp only [not_forall] at h0
  obtain ⟨b, hb⟩ := h0
  have he_pure : ∀ (c : Fin N) (x : I g), (X.G g).ty (Sum.inl x) ≠ a →
      (fun δ => (S g).tan (em δ)) c x = 0 := by
    intro c x hx
    exact tan_pure (S g) (em c) x (by rw [hty c]; exact hx)
  obtain ⟨γ, hγ, hγeq⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hAlt g a 1 odd_one hd S t hT (Fin N) (Fin X.n)
    (fun δ => (S g).tan (em δ)) v' he_pure hint hpure b
  have h91 := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin X.n) (fun δ => (S g).tan (em δ)) v'
  have hsingle : Finsupp.single (Sum.inr b) 1 ≤ μ :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = μ' + Finsupp.single (Sum.inr b) 1 :=
    ⟨μ - Finsupp.single (Sum.inr b) 1, (tsub_add_cancel_of_le hsingle).symm⟩
  have hl' : ∑ c, μ' (Sum.inl c) < V.l ^ 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμl
  have hr' : ∑ b', μ' (Sum.inr b') < V.l :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμr
  have hbl : μ' (Sum.inr b) + 1 < V.l := by
    refine lt_of_le_of_lt ?_ hμr
    have := Finset.single_le_sum (f := fun b' => (μ' + Finsupp.single (Sum.inr b) 1 : Fin N ⊕ Fin X.n →₀ ℕ) (Sum.inr b'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using this
  have hunit : V.v ((μ' (Sum.inr b) : C) + 1) = 0 := by
    have hc : ((μ' (Sum.inr b) : C) + 1) = ((μ' (Sum.inr b) + 1 : ℕ) : C) := by push_cast; ring
    rw [hc]
    exact ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime V.v V.v_l
      (Nat.coprime_of_lt_prime (by omega) hbl V.l_prime)
  have hne : ((μ' (Sum.inr b) : C) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  set Φ : Fin X.n → Fin N → C := fun b c => ∑ κ : J g, ∑ k : I (1 - g),
    -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k with hΦ
  set F := X.hM g a 1 (fun δ => (S g).tan (em δ)) v' - mainM V 1 Φ with hF
  have hcoeff : MvPowerSeries.coeff (μ' + Finsupp.single (Sum.inr b) 1) F =
      ((μ' (Sum.inr b) : C) + 1)⁻¹ * MvPowerSeries.coeff μ' (MvPowerSeries.pderiv (R := C) (Sum.inr b) F) := by
    rw [MvPowerSeries.coeff_pderiv]
    field_simp
  rw [hcoeff]
  refine VF.Ge.mul_int (inv_unit_int hunit) ?_
  set G : MvPowerSeries (Fin N) C :=
    (∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • linPull (fun δ => (S g).tan (em δ)) ((S g).ze (t g) κ)) -
      (V.l : C)⁻¹ • ∑ c : Fin N, Φ b c • (MvPowerSeries.X c : MvPowerSeries (Fin N) C) ^ V.l with hG
  have hsplit : MvPowerSeries.pderiv (R := C) (Sum.inr b) F =
      MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2))
        (fun c => toW g ((fun δ => (S g).tan (em δ)) c)) (fun b => toW (1 - g) (v' b))) γ +
      MvPowerSeries.rename Sum.inl G := by
    rw [hF, map_sub, hγeq, pderiv_inr_mainM_one V Φ b]

    simp only [h91.1, hG, map_sub, map_sum, map_smul]
    abel
  rw [hsplit, map_add (f := _)]
  refine VF.Ge.add ?_ ?_
  · have h2 : ∀ j g : Fin 2, j = g ∨ j = 1 - g := by decide
    refine GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set C V (Fin N ⊕ Fin X.n) (WV I)
      (fun ν => ∑ c, ν (Sum.inl c) < V.l ^ 2 ∧ ∑ b', ν (Sum.inr b') < V.l) ?_ γ _ hγ ?_ ?_ μ' ⟨hl', hr'⟩
    · intro ν ν' hle hP
      exact ⟨lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inl c)) hP.1,
        lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inr c)) hP.2⟩
    · rintro ⟨j, x⟩
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT j).1 x)
      · simp only
        rw [h91.2, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT (1 - g)).1 x)
    · rintro ⟨j, x⟩ ν hP
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1]
        apply ge_coeff_rename_inl V
        intro ν' hν'

        rw [(GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I j) (J j) (X.G j) (S j) (t j) (hT j) N em hal ν'
        (by rw [hν']; exact hP.1)).1 x, map_sum]
        apply VF.Ge.sum
        intro δ _
        split_ifs
        · rw [MvPowerSeries.coeff_X]
          split_ifs
          exacts [VF.Ge.one, VF.Ge.zero 0]
        · rw [map_zero]
          exact VF.Ge.zero 0
      · simp only
        rw [h91.2]
        apply ge_coeff_rename_inr V
        intro ν' hν'
        exact GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt C V d (I (1 - g)) (J (1 - g)) (X.G (1 - g)) (S (1 - g)) (t (1 - g))
          (hT (1 - g)) X.n v' hint ν' (by rw [hν']; exact hP.2) x
  · apply ge_coeff_rename_inl V
    intro ν hν
    have hdeg : ν.degree < V.l ^ 2 := by rw [hν]; exact hl'
    have h19 := (GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I g) (J g) (X.G g) (S g) (t g) (hT g) N em hal ν hdeg).2
    have hz : MvPowerSeries.coeff ν G = 0 := by

      rw [hG, map_sub, map_sum]

      simp only [MvPowerSeries.coeff_smul, h19, map_neg, map_sum, hΦ]
      have hL : (V.l : C) ≠ 0 := VF.l_ne_zero
      rw [sub_eq_zero]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
      rw [neg_inj, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [hz]
    exact VF.Ge.zero 0

end GlobalTheory.MainTerm
end
