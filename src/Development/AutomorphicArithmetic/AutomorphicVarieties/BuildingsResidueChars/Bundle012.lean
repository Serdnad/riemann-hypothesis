module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle004
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Hi

private noncomputable def rhoT {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) :
    Representation Ω (A × B) (Matrix m n Ω) where
  toFun k :=
    { toFun := fun v => (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ)
      map_add' := fun v w => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by simp [smul_comm c] }
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' k k' := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mul_assoc, smul_smul, mul_comm]

private theorem rhoT_apply {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) (k : A × B)
    (v : Matrix m n Ω) :
    rhoT σ ξ ψ k v = (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ) := rfl

private theorem mulVec_row {Ω m n : Type} [Field Ω] [Fintype n] (M : Matrix n n Ω) (v : Matrix m n Ω) (i : m) :
    M *ᵥ v i = (v * Mᵀ) i := by
  ext k
  simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → X.Free τ θ U → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ v : Fin N → Fin m → Fin (W.d + 1) → Ω, ∃ F ∈ X.ClO W τ U c φ, ∀ n i k, X.unt m W F i (x n) k = v n i k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hφ hθ hfree N x hcov huniq v
  obtain ⟨ψ, hψ⟩ := UpperTheory.exists_iwahori_character_extending_torus_character Gp X.I Ωˣ c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)
    (fun t ht => by simp [hφ t ht])
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  set τ' := (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ with hτ'
  let j : U × X.I.Iw c →* Ga × Gp := (X.Ub.subtype.comp U.subtype).prodMap (X.I.Iw c).subtype
  have hj : ∀ k : U × X.I.Iw c, j k = (((k.1 : X.Ub) : Ga), (k.2 : Gp)) := fun _ => rfl
  obtain ⟨Φ, h1, h2, h3⟩ := UpperTheory.exists_automorphic_function_with_values_on_coset_reps Γ (Ga × Gp) (U × X.I.Iw c) Ω
    (Matrix (Fin m) (Fin (W.d + 1)) Ω) (Fin N) X.glob j
    (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ) x
    (fun g => by
      obtain ⟨γ, i, u, hu, b, hb, h⟩ := hcov g
      exact ⟨γ, i, (⟨u, hu⟩, ⟨b, hb⟩), h⟩)
    (fun i i' γ k h => huniq i i' γ k.1 k.1.2 k.2 k.2.2 h)
    (fun i γ k h => by
      obtain ⟨hc, hb, e⟩ := hfree (x i) γ k.1 k.1.2 k.2 (hle k.2.2) h
      refine LinearMap.ext fun w => ?_
      have hξ : (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) = (W.χ ⟨k.2, X.I.T_le hb⟩ : Ω) • (1 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) := by
        ext a b
        rw [W.central ⟨k.2, X.I.T_le hb⟩ hc a b]
        simp [Matrix.one_apply]
      have e' : algebraMap O Ω (θ ⟨k.2, hb⟩) • (τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) = 1 := by
        ext a b
        have := congrArg (algebraMap O Ω) (congrFun (congrFun e a) b)
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply] at this ⊢
        rw [apply_ite (algebraMap O Ω), map_one, map_zero] at this
        exact this
      rw [hθ] at e'
      rw [rhoT_apply, (hψ k.2).2.2 hb]
      show algebraMap O Ω (φ ⟨k.2, hb⟩) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) * w *
        (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = w
      rw [hξ, transpose_smul, transpose_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        ← Matrix.smul_mul, e', Matrix.one_mul])
    (fun n => Matrix.of (v n))
  have h2' : ∀ g (k : U × X.I.Iw c), (ψ k.2 : Ω) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) *
      Φ (g * j k) * (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = Φ g := by
    intro g k
    have := congrArg (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ k) (h2 g k)
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one] at this
    exact this
  have hp : ∀ b : X.I.Iw c, X.rpF Ω (W.d + 1) m b
      (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) =
      (((ψ b)⁻¹ : Ωˣ) : Ω) • (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) := by
    intro b
    funext i g
    show (Φ (g * j (1, b)) * (W.ξ (g.2 * b) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i =
      ((((ψ b)⁻¹ : Ωˣ) : Ω) • (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i
    rw [← h2' g (1, b)]
    simp [smul_smul, Matrix.mul_assoc]
  refine ⟨fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i, ⟨⟨fun i _ γ g => ?_, fun u hu => ?_⟩,
    fun b hb => ?_, fun b hb => ?_, fun t => ?_⟩, fun n i k => ?_⟩
  · show _ = _ *ᵥ (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i
    rw [mulVec_row]
    simp [h1, Matrix.mul_assoc]
  · funext i g k
    show ((τ' u : Matrix (Fin m) (Fin m) Ω) *
      (Φ (g * j (⟨u, hu⟩, 1)) * (W.ξ (g.2 * 1) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i k = (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i k
    rw [← h2' g (⟨u, hu⟩, 1)]
    simp [Matrix.mul_assoc]
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).1 hb] at this
    simpa using this
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_right hb
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).2.1 hb] at this
    simpa using this
  · have hb' : (t : Gp) ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_right t.2)
    have := hp ⟨t, hb'⟩
    rw [(hψ ⟨t, hb'⟩).2.2 t.2] at this
    exact this
  · rw [Frame.unt_apply]
    show (_ *ᵥ (Φ (x n) * (W.ξ (x n).2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) k = _
    rw [mulVec_row, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one, h3]
    rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_step {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (φ : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ)
    (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) :
    ∀ F ∈ X.Cl τ W.ξ U (c + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Cl τ W.ξ U c φ := by
  classical
  intro F hF
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem
  have hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F =
      (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F := by
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · rw [(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)

theorem UpperTheory.classicalForms_level_monotone_and_Up_stable :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type)
      [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ)
      (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ),
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ) ∧
      (∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ) ∧
      ∀ e n : ℕ, e ≤ n → ∀ F ∈ X.ClO W τ U (c + e) φ,
        (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F ∈ X.ClO W τ U c φ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hφ
  have mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ := by
    intro c' hc F hF
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hF
    refine Submodule.mem_inf.2 ⟨h1, ?_⟩
    exact ⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩
  have step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ,
      X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ := by
    intro e F hF
    exact lower_step X W _ _ U (c + e)
      (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF
  have down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ := by
    intro e
    induction e with
    | zero =>
      intro F hF
      simpa using hF
    | succ e ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step e F hF)
  have stay : ∀ k, ∀ F ∈ X.ClO W τ U c φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ k) F ∈ X.ClO W τ U c φ := by
    intro k
    induction k with
    | zero =>
      intro F hF
      simpa using hF
    | succ k ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step 0 F (mono _ (Nat.le_succ c) hF))
  refine ⟨mono, fun F hF => step 0 F (mono _ (Nat.le_succ c) hF), ?_⟩
  intro e n hen F hF
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hen
  rw [add_comm e k, pow_add, mul_apply_eq_comp]
  exact stay k _ (down e F hF)
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_one {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c d : ℕ) (hcd : c ≤ d) (v : M) (hN : v ∈ fixd π I.N) (hT : v ∈ fixd π (I.Tc c))
    (hm : v ∈ fixd π (I.Nm (d + 1))) :
    I.uOp π I.z v ∈ fixd π I.N ∧ I.uOp π I.z v ∈ fixd π (I.Tc c) ∧ I.uOp π I.z v ∈ fixd π (I.Nm d) := by
  obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π I.z I.z I.z_mem I.z_mem v hN
  refine ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht], fun y hy => ?_⟩
  exact (uOpLevel G I A M π d).2.1 v hN (fun t ht => hT t (I.Tc_anti hcd ht)) hm y (Subgroup.mem_sup_right hy)

private theorem lower_many {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (π : Representation A G M) (c n : ℕ) : ∀ v : M, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) →
      v ∈ fixd π (I.Nm (c + n)) → (I.uOp π I.z ^ n) v ∈ fixd π (I.Nm c) := by
  induction n with
  | zero => exact fun v _ _ hm => by simpa using hm
  | succ n ih =>
    intro v hN hT hm
    obtain ⟨h1, h2, h3⟩ := lower_one I π c (c + n) (Nat.le_add_right c n) v hN hT hm
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ h1 h2 h3

theorem UpperTheory.uOperator_pow_eventually_invariant_mod_pow :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ f ∈ X.Amb m θ, ∀ k c : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ y ∈ X.I.Nm c, X.rp A m y ((X.U A m X.I.z ^ n) f) - (X.U A m X.I.z ^ n) f ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m θ _ f hf k c hc
  obtain ⟨-, h2, h3, h4⟩ := hf
  obtain ⟨c1, hc1⟩ := h4 k
  refine ⟨c1, fun n hn y hy => ?_⟩
  let φ : X.Fn A m →ₗ[A] X.Fn (A ⧸ maximalIdeal A ^ k) m := X.mapFn
  have hφ : ∀ f g i, φ f g i = Ideal.Quotient.mk _ (f g i) := fun _ _ _ => rfl
  have hnat : ∀ b f, φ (X.rp A m b f) = X.rp _ m b (φ f) := fun _ _ => rfl
  have hN : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.N := fun x hx => by rw [← hnat, h2 x hx]
  have hT : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Tc c) := fun t ht => by
    have ht' := X.I.Tc_le _ ht
    have := hc ⟨t, ht'⟩⁻¹ (inv_mem ht)
    rw [← hnat, h3 ⟨t, ht'⟩]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    have h6 := Ideal.mul_mem_right (f g i) _ this
    rw [map_inv] at h6
    convert h6 using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm : φ f ∈ fixd (X.rp (A ⧸ maximalIdeal A ^ k) m) (X.I.Nm (c + n)) := fun w hw => by
    rw [← hnat]
    funext g i
    rw [hφ, hφ, Ideal.Quotient.eq]
    exact hc1 w (X.I.Nm_anti (by omega) hw) g i
  have hpow : ∀ j : ℕ, φ ((X.U A m X.I.z ^ j) f) =
      (X.I.uOp (X.rp (A ⧸ maximalIdeal A ^ k) m) X.I.z ^ j) (φ f) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
      exact uOpNat Gp X.I A _ (X.rp A m) _ _ (X.rp (A ⧸ maximalIdeal A ^ k) m) φ.toAddMonoidHom X.I.z X.I.z_mem _
        (fun _ _ => rfl)
  have h7 := lower_many X.I (X.rp (A ⧸ maximalIdeal A ^ k) m) c n _ hN hT hm y hy
  rw [← hpow, ← hnat] at h7
  simp only [Frame.valIn, Submodule.mem_pi]
  intro g _ i _
  have h9 := congrFun (congrFun h7 g) i
  rw [hφ, hφ, Ideal.Quotient.eq] at h9
  exact h9
end

section

open MulAction in
theorem UpperTheory.symmetric_fiber_master_formula :
    UpperTheory.V.Z.Sym.Glob.Fib.Master := by
  intro Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab
  classical
  haveI hSN : S.Normal := ⟨fun s hs g => by
    have h := S.mul_mem (hcomm g s) hs
    simpa [mul_assoc] using h⟩
  have hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype := MonoidHom.ext fun γ => hι₁ γ
  have hsub : Γ₁ ≤ S.comap ι := fun γ hγ => by
    have h := (ι₁ ⟨γ, hγ⟩).2
    rw [hι₁] at h
    exact h
  have hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite := fun g =>
    UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)

  have hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 := by
    have hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'} := by
      intro z hz
      have hz' : (z : Γ) ∈ Γ₀ := Subgroup.mem_subgroupOf.1 hz
      have h := htriv _ hz' ((1 : G) : G ⧸ U')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h
      have h' : ι z ∈ U' := by simpa using U'.inv_mem h
      simpa [hι₁] using h'
    haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype
    exact Nat.card_pos.ne'
  have hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    refine UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_
    · obtain ⟨T, hT1⟩ := hfinT 1
      refine ⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩
      have e' := congrArg (Subtype.val) e
      simpa [hι₁] using e'
    · have h := hstab ((1 : G) : G ⧸ U')
      rwa [MulAction.stabilizer_quotient] at h
  have hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) /
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
    have h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
    have h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    exact div_pos (mul_pos h1 h2) h3
  intro I _ x Ux Φ hij hcov hUx hΦl hΦr
  rw [UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcover := UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx
    (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T, fun s => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 s
      exact ⟨h, t, ht, u, (hUx i u).2 hu, e⟩)
    hfinU'
  have hone := UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩
      have e' : s = ι h * t * u := by
        have e2 := congrArg (Subtype.val) e
        simpa [hι₁] using e2
      rw [e']
      group)
    hstab hd hn
  rw [hcover, hcomp]
  have hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U'
      ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hone
  rw [hC]
  push_cast
  ring
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem int_of_norm_one {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] {Δ τ : K} (h : IsLoc O Δ) (hτ : ¬ IsSquare (τ ^ 2 - 4)) (e : Etau K τ)
    (hn : QuadraticAlgebra.norm e = 1) : IsIntegral O e := by
  classical
  haveI := h.frac
  have hN : e.re * e.re + τ * e.re * e.im - (-1) * e.im * e.im = 1 := by
    have h' := hn
    rw [QuadraticAlgebra.norm_def] at h'
    exact h'
  by_cases hq : e.im = 0
  · have hp : (e.re - 1) * (e.re + 1) = 0 := by
      rw [hq] at hN
      linear_combination hN
    rcases mul_eq_zero.mp hp with h1 | h1
    · have he : e = 1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one
    · have he : e = -1 := by
        ext
        · simp
          linear_combination h1
        · simp [hq]
      rw [he]
      exact isIntegral_one.neg
  · have h2K : (2 : K) ≠ 0 := by
      have h2 := h.two.map (algebraMap O K)
      rw [map_ofNat] at h2
      exact h2.ne_zero
    have nz : ∀ x y : K, y ≠ 0 → x * x + τ * x * y + y * y ≠ 0 := by
      intro x y hy hxy
      apply hτ
      refine ⟨2 * x / y + τ, ?_⟩
      field_simp
      linear_combination (-4) * hxy
    obtain ⟨t, ht⟩ : ∃ t : O, algebraMap O K t = QuadraticAlgebra.trace e := by
      by_contra hne
      push_neg at hne
      have hTd : QuadraticAlgebra.trace e = 2 * e.re + τ * e.im := QuadraticAlgebra.trace_def e
      set T := QuadraticAlgebra.trace e with hTdef
      have hT0 : T ≠ 0 := fun h0 => hne 0 (by rw [map_zero, h0])
      rcases ValuationRing.isInteger_or_isInteger O T with ⟨t, ht⟩ | ⟨s, hs⟩
      · exact hne t ht
      · have hsm : s ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          obtain ⟨u, rfl⟩ := hu
          apply hne (↑u⁻¹)
          rw [map_units_inv, hs, inv_inv]
        obtain ⟨r, hr, -⟩ := sqrtO O K Δ h (1 - 4 * s ^ 2) 1 isUnit_one (by
          have e' : (1 - 4 * s ^ 2) - 1 ^ 2 = s * (-(4 * s)) := by ring
          rw [e']
          exact Ideal.mul_mem_right _ _ hsm)
        have hTS : T * algebraMap O K s = 1 := by
          rw [hs]
          exact mul_inv_cancel₀ hT0
        have hR : (algebraMap O K r) ^ 2 = 1 - 4 * (algebraMap O K s) ^ 2 := by
          rw [← map_pow, hr, map_sub, map_one, map_mul, map_pow, map_ofNat]
        apply nz (-τ * e.im - T * algebraMap O K r) (2 * e.im) (mul_ne_zero h2K hq)
        linear_combination T ^ 2 * hR - 4 * (T * algebraMap O K s + 1) * hTS + 4 * hN +
          (T + 2 * e.re + τ * e.im) * hTd
    exact isIntegral_of_trace_norm t 1 ht.symm (by rw [hn, map_one])

private theorem norm_quo {K : Type} [Field K] {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  simp only [quo, map_mul, QuadraticAlgebra.norm_star]
  rw [← map_mul, Units.mul_inv, map_one]

theorem UpperTheory.compactTorusUnits_eq_top_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → Cint O τ = ⊤ := by
  intro O K _ _ _ _ _ Δ τ h _ hτ
  rw [eq_top_iff]
  intro z _
  exact ⟨int_of_norm_one h hτ _ (norm_quo z), int_of_norm_one h hτ _ (norm_quo z⁻¹)⟩
end
