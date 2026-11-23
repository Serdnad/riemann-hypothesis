module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle005
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}

theorem deg_mono {d : ℕ} {g : Module.End ℂ (TV n M (Fin m))} (h : Deg E d g) :
    ∀ d', d ≤ d' → Deg E d' g := by
  induction h with
  | one d => intro d' _; exact Deg.one d'
  | add _ _ ih1 ih2 => intro d' h; exact Deg.add (ih1 d' h) (ih2 d' h)
  | smul c _ ih => intro d' h; exact Deg.smul c (ih d' h)
  | @om d g p _ ih =>
    intro d' h
    obtain ⟨k, rfl⟩ : ∃ k, d' = k + 1 := ⟨d' - 1, by omega⟩
    exact Deg.om p (ih k (by omega))
  | perm σ _ ih => intro d' h; exact Deg.perm σ (ih d' h)

theorem deg_mul {d d' : ℕ} {g h : Module.End ℂ (TV n M (Fin m))} (hg : Deg E d g) (hh : Deg E d' h) :
    Deg E (d + d') (g * h) := by
  induction hh with
  | one d' => rw [mul_one]; exact deg_mono hg _ (by omega)
  | add _ _ ih1 ih2 => rw [mul_add]; exact Deg.add ih1 ih2
  | smul c _ ih => rw [mul_smul_comm]; exact Deg.smul c ih
  | om p _ ih => rw [← mul_assoc]; exact Deg.om p ih
  | perm σ _ ih => rw [← mul_assoc]; exact Deg.perm σ ih

theorem deg_zero (d : ℕ) : Deg E d (0 : Module.End ℂ (TV n M (Fin m))) := by
  have := Deg.smul (E := E) (0 : ℂ) (Deg.one (P := Fin m) d)
  rwa [zero_smul] at this

theorem deg_sum {d : ℕ} (s : Finset (Fin m)) (f : Fin m → Module.End ℂ (TV n M (Fin m)))
    (hf : ∀ i ∈ s, Deg E d (f i)) : Deg E d (∑ i ∈ s, f i) := by
  classical
  exact Finset.sum_induction f (Deg E d) (fun _ _ ha hb => Deg.add ha hb) (deg_zero d) hf

theorem deg_xJ (j : Fin m) : Deg E 1 (xJ E j) := by
  unfold xJ
  refine Deg.add ?_ (deg_sum _ _ fun i _ => ?_)
  · have := Deg.om (E := E) j (Deg.one (P := Fin m) 0)
    rwa [one_mul] at this
  · have := Deg.perm (E := E) (Equiv.swap i j) (Deg.one (P := Fin m) 1)
    rwa [one_mul] at this

theorem deg_factor (i j : Fin m) (c : Prop) [Decidable c] :
    Deg E (if c then 1 else 0) (if c then xJ E i - xJ E j + 1 else 1) := by
  split_ifs
  · refine Deg.add ?_ (Deg.one 1)
    rw [sub_eq_add_neg]
    refine Deg.add (deg_xJ i) ?_
    have h1 := Deg.smul (-1 : ℂ) (deg_xJ (E := E) j)
    rwa [neg_one_smul] at h1
  · exact Deg.one 0

theorem deg_prod : ∀ (k : ℕ) (f : Fin k → Module.End ℂ (TV n M (Fin m))) (e : Fin k → ℕ),
    (∀ i, Deg E (e i) (f i)) → Deg E (∑ i, e i) (List.ofFn f).prod := by
  intro k
  induction k with
  | zero => intro f e _; simpa using Deg.one (E := E) (P := Fin m) 0
  | succ k ih =>
    intro f e hf
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact deg_mul (hf 0) (ih _ _ fun i => hf i.succ)

theorem npairs_eq (col : Fin m → ℕ) :
    (∑ j : Fin m, ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0) = npairs col := by
  unfold npairs
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]

theorem deg_colD {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) :
    Deg E (npairs col) (colD E col : Module.End ℂ (TV n M (Fin m))) := by
  have h := deg_prod m
    (fun j => (List.ofFn fun i : Fin m => if i < j ∧ col i = col j then xJ E i - xJ E j + 1 else 1).prod)
    (fun j => ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0)
    (fun j => deg_prod m _ _ (fun i => deg_factor i j _))
  rw [npairs_eq] at h
  exact h

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

section Int

variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem int_exists (ρ : Γ → Module.End ℂ M) (y : M)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y)))
    (hcont : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun γ => lam (ρ γ y)) {g : Γ → ℂ} (hg : Continuous g) :
    ∃ x : M, ∀ lam : M →ₗ[ℂ] ℂ, lam x = ∫ k, g k * lam (ρ k y) ∂μ := by
  classical
  haveI := hfin
  set V := Submodule.span ℂ (Set.range fun γ => ρ γ y) with hV
  let b := Module.finBasis ℂ V
  have hext : ∀ i, ∃ f : M →ₗ[ℂ] ℂ, f ∘ₗ V.subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose e he using hext
  have hmem : ∀ k, ρ k y ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hrepr : ∀ k, ρ k y = ∑ i, e i (ρ k y) • (b i : M) := by
    intro k
    have hc : ∀ i, e i (ρ k y) = b.repr ⟨ρ k y, hmem k⟩ i := fun i => by
      have := LinearMap.congr_fun (he i) ⟨ρ k y, hmem k⟩
      simpa using this
    simp_rw [hc]
    have h := congrArg Subtype.val (b.sum_repr ⟨ρ k y, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hint : ∀ i, Integrable (fun k => g k * e i (ρ k y)) μ := fun i =>
    integrable_of_cont μ (hg.mul (hcont (e i)))
  refine ⟨∑ i, (∫ k, g k * e i (ρ k y) ∂μ) • (b i : M), fun lam => ?_⟩
  have hpt : ∀ k, g k * lam (ρ k y) = ∑ i, g k * e i (ρ k y) * lam (b i) := by
    intro k
    conv_lhs => rw [hrepr k]

    simp [map_sum, Finset.mul_sum, mul_assoc]
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hint i).mul_const _)]

  simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
theorem mono_left (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) (γ k : Γ) :
    ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k =
      (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
  have hd : ∀ τ, (κ τ γ).det ≠ 0 := fun τ => det_ne hK τ γ
  have hc : (∏ τ, (κ τ γ).det ^ (-c τ)) * ∏ τ, (κ τ γ).det ^ (c τ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [← zpow_add₀ (hd τ)]
    simp
  calc ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k
      = ∑ J : Fin m → Fin n, (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, (κ (lab p) γ (I p) (J p) * κ (lab p) k (J p) (K p)) := by
        apply Finset.sum_congr rfl
        intro J _
        simp only [mono, Finset.prod_mul_distrib]
        ring
    _ = (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, ∑ j, κ (lab p) γ (I p) j * κ (lab p) k j (K p) := by
        rw [Fintype.prod_sum, Finset.mul_sum]
    _ = (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
        simp only [mono, hK.mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
        rw [← mul_assoc, ← mul_assoc, hc, one_mul]

theorem tensor_exists [IsTopologicalGroup Γ] [μ.IsMulLeftInvariant] {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (y : M) {m : ℕ} (lab : Fin m → ι)
    (c : ι → ℤ) (K : Fin m → Fin n) :
    ∃ ξ : TV n M (Fin m), (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ (-c τ)) • ξ) ∧
      ∀ I (lam : M →ₗ[ℂ] ℂ), lam (ξ I) = ∫ k, mono κ lab c I K k * lam (ρ k y) ∂μ := by
  classical
  choose ξ hξ using fun I : Fin m → Fin n =>
    int_exists μ ρ y (hG.fin y) (hG.cont y) (g := mono κ lab c I K) (mono_cont hK lab c I K)
  refine ⟨ξ, fun γ => ?_, hξ⟩
  have hLc : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun k => lam (ρ (γ * k) y) := by
    intro lam
    simpa [hG.mul, Module.End.mul_apply] using hG.cont y (lam ∘ₗ ρ γ)
  have hD : (∏ τ, (κ τ γ).det ^ (-c τ)) = (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ := by
    simp [_root_.zpow_neg, Finset.prod_inv_distrib]
  funext I
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro lam
  rw [map_sub, sub_eq_zero]
  have h1 : ∀ J, lam (ρ γ (ξ J)) = ∫ k, mono κ lab c J K k * lam (ρ (γ * k) y) ∂μ := by
    intro J
    have := hξ J (lam ∘ₗ ρ γ)
    simpa [hG.mul, Module.End.mul_apply] using this
  simp [actT, h1, hξ I lam]
  simp_rw [← integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum]
  · rw [← integral_mul_left_eq_self
      (fun x => (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ * (mono κ lab c I K x * lam (ρ x y))) γ]
    congr 1
    funext k
    rw [← mul_assoc, ← hD, ← mono_left hK lab c I K γ k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    ring
  · intro J _
    exact integrable_of_cont μ (continuous_const.mul ((mono_cont hK lab c J K).mul (hLc lam)))

end Int

end SWS

theorem swStart_holds : SWStart := by
  unfold SWStart
  intro n M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG φ hφ
  classical
  letI : MeasurableSpace Γ := borel Γ
  haveI : BorelSpace Γ := ⟨rfl⟩
  obtain ⟨H, hH⟩ := SWS.exists_half bar hK.invol hK.ne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  have hf : Continuous fun k => φ (ρ k y) := hG.cont y φ
  have h1 : φ (ρ 1 y) ≠ 0 := by simpa [hG.one] using hy
  obtain ⟨g, ⟨m, lab, c, I, K, hlab, rfl⟩, hg⟩ :=
    SWS.nonvanish (Measure.haar : Measure Γ) hK hH hf 1 h1
  obtain ⟨ξ, hξ1, hξ2⟩ := SWS.tensor_exists (Measure.haar : Measure Γ) hK hG y lab c K
  refine ⟨m, lab, -c, ξ, ?_, ?_, I, 1, Subalgebra.one_mem _, ?_⟩
  · intro p q h
    exact (hH (lab q)).1 (hlab q) (h ▸ hlab p)
  · intro γ
    rw [hξ1 γ]
    simp
  · simpa [hξ2 I φ] using hg

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
@[simp] theorem lift_apply (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := rfl

omit [Fintype P] in
theorem eAt_apply (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> simp

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_apply (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := rfl

omit [Fintype P] in
theorem tE_apply (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by
  simp only [tE, LinearMap.add_apply, Pi.add_apply, lift_apply, LinearMap.sum_apply, Finset.sum_apply, eAt_apply]

omit [Fintype P] in
theorem Om_apply (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by
  simp only [Om, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, lift_apply, eAt_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I p)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero]
  · simp

omit [Fintype P] [DecidableEq P] in
theorem pm_mul (σ τ : Equiv.Perm P) : (pm (σ * τ) : Module.End ℂ (TV n M P)) = pm σ * pm τ := rfl

omit [Fintype P] [DecidableEq P] in
@[simp] theorem pm_one : (pm 1 : Module.End ℂ (TV n M P)) = 1 := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_mul (B B' : Module.End ℂ M) : (lift (B * B') : Module.End ℂ (TV n M P)) = lift B * lift B' := rfl

omit [Fintype P] [DecidableEq P] in
theorem lift_comm_pm (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := rfl

def liftA (n : ℕ) (M P : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (TV n M P) where
  toFun := lift
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype P] in
theorem lift_comm_eAt (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, eAt_apply]
  split_ifs <;> simp

theorem alt_apply (G : Finset (Equiv.Perm P)) (f : TV n M P) (I : P → Fin n) :
    alt G f I = ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ σ) := by
  simp only [alt, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, pm_apply]

theorem cA_apply {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA col b f = alt (colG col) f b := rfl

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem curF_apply {m k : ℕ} (f : TV n M (Fin (m + k))) (J : Fin k → Fin n) (I : Fin m → Fin n) :
    curF n M m k f J I = f (Fin.append I J) := rfl

end PositivityTheory.Rg.Cz

end
end
