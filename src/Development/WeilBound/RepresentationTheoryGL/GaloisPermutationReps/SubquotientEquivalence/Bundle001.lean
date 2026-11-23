module

public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace DepthZeroEigenvalues

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_good {y : WD h} (hi : IsIrrWD y) (ht : IsTameWD y) :
    ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧ a.ρ.IsIrreducible ∧
      ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 := by
  obtain ⟨m, a, rfl, ha⟩ := hi
  obtain ⟨m', b, hb, hbt⟩ := ht
  have hba : b.Iso a := WD.mk_eq_mk.mp hb
  exact ⟨m, a, rfl, ha, fun σ hσ => hba.ρ_eq_one (hbt σ hσ)⟩

theorem isUnit_rho {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) : IsUnit (a.ρ σ) :=
  (Group.isUnit σ).map a.ρ

theorem eig_prod {m : ℕ} (a : WDRep h (Fin m → ℂ)) (σ : Weil h) :
    ((WD.mk a).eig σ).prod = LinearMap.det (a.ρ σ) := by
  rw [WD.eig_mk, Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)]

theorem card_res (w : HeightOneSpectrum (𝓞 E)) : Nat.card 𝓀[w.adicCompletion E] = normV w :=
  resCard_eq_normV w

end DepthZeroEigenvalues

open DepthZeroEigenvalues in
theorem st3 : St1a → St1b → St2 → St3a → St3 := by
  intro h1a h1b h2 h3a E Ω _ _ _ _ _ A w h φ hφ n c hn
  obtain ⟨γ, hγ1, hγ2⟩ := h2 E Ω A w h φ hφ
  have hq : Nat.card 𝓀[w.adicCompletion E] = normV w := card_res w
  have : Finite 𝓀[w.adicCompletion E] := inferInstance
  obtain ⟨lab, hlab1, hlab2⟩ := h3a 𝓀[w.adicCompletion E] n hn
  set q := Nat.card 𝓀[w.adicCompletion E] with hqdef

  let Pz : WD h → ℂ → Prop := fun y z => ∃ (m : ℕ) (a : WDRep h (Fin m → ℂ)), WD.mk a = y ∧
    a.ρ.IsIrreducible ∧ (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) ∧
    Module.End.HasEigenvalue (a.ρ γ) z ∧ ExactPer q n z
  have hex : ∀ y ∈ TameSet φ n c, ∃ z, Pz y z := by
    intro y hy
    obtain ⟨m, a, rfl, hai, hat⟩ := exists_good hy.1 hy.2.1
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    obtain ⟨hc, hirr⟩ := hγ1 m a hat
    obtain ⟨z, hz1, hz2⟩ := h1a (Fin m → ℂ) (normV w) (a.ρ γ) (a.ρ φ) (isUnit_rho a γ)
      (isUnit_rho a φ) hc (hirr hai)
    refine ⟨z, m, a, rfl, hai, hat, hz1, ?_⟩
    rw [hm] at hz2
    rw [hq]; exact hz2
  let zf : WD h → ℂ := fun y => Classical.epsilon (Pz y)
  have hzf : ∀ y ∈ TameSet φ n c, Pz y (zf y) := fun y hy => Classical.epsilon_spec (hex y hy)
  refine ⟨fun y => lab (zf y), ?_, ?_⟩
  · intro y hy
    obtain ⟨_, _, _, _, _, _, hz⟩ := hzf y hy
    exact hlab1 _ hz
  · intro y hy y' hy' heq
    obtain ⟨m, a, rfl, hai, hat, hz1, hz2⟩ := hzf y hy
    obtain ⟨m', a', rfl, hai', hat', hz1', hz2'⟩ := hzf y' hy'
    obtain ⟨i, hi⟩ := hlab2 _ _ hz2 hz2' heq
    have hm : Module.finrank ℂ (Fin m → ℂ) = n := by
      have := hy.2.2.1
      rwa [WD.lpDim_mk] at this
    have hm' : Module.finrank ℂ (Fin m' → ℂ) = n := by
      have := hy'.2.2.1
      rwa [WD.lpDim_mk] at this
    have hdet : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← eig_prod, ← eig_prod, hy.2.2.2, hy'.2.2.2]
    obtain ⟨hc, -⟩ := hγ1 m a hat
    obtain ⟨hc', -⟩ := hγ1 m' a' hat'
    rw [← hq] at hc hc'
    obtain ⟨e, he1, he2⟩ := h1b (Fin m → ℂ) (Fin m' → ℂ) q n i (a.ρ γ) (a.ρ φ) (a'.ρ γ) (a'.ρ φ)
      (zf (WD.mk a)) hn hm hm' (isUnit_rho a φ) (isUnit_rho a' φ) hc hc' hz2 hz1 (hi ▸ hz1') hdet
    exact WD.mk_eq_mk.mpr (hγ2 m m' a a' hat hat' hai hai' e he1 he2)

end PositivityTheory.Rg.DzCount
end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

lemma pow_pow_pow_add (z : ℂ) (q a b : ℕ) : (z ^ q ^ a) ^ q ^ b = z ^ q ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

lemma eigenvector_maps_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) : M (G v) = z ^ q • G v := by
  have hpow : ∀ k : ℕ, (M ^ k) v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have h := congrArg (fun T : Module.End ℂ V => T v) hMG
  simp only [Module.End.mul_apply] at h
  rw [h, hpow, map_smul]

lemma eigenvector_iterate_power {V : Type} [AddCommGroup V] [Module ℂ V] (q : ℕ) (M G : Module.End ℂ V)
    (hMG : M * G = G * M ^ q) (z : ℂ) (v : V) (hv : M v = z • v) :
    ∀ i : ℕ, M ((G ^ i) v) = z ^ q ^ i • (G ^ i) v := by
  intro i
  induction i with
  | zero => simpa using hv
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, eigenvector_maps_power q M G hMG _ _ ih, ← pow_mul, ← pow_succ]

theorem st1a : St1a := by
  classical
  intro V _ _ _ q M G hM hG hMG hirr
  obtain ⟨hnt, hU⟩ := hirr
  have hGinj : ∀ i : ℕ, Function.Injective (G ^ i) := fun i =>
    ((Module.End.isUnit_iff _).mp (hG.pow i)).1
  have hMinj : Function.Injective M := ((Module.End.isUnit_iff _).mp hM).1
  have hfin : Set.Finite {μ | M.HasEigenvalue μ} := M.finite_hasEigenvalue
  have hstep : ∀ μ, M.HasEigenvalue μ → M.HasEigenvalue (μ ^ q) := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv' : M v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := G v) ⟨?_, ?_⟩
    · exact Module.End.mem_eigenspace_iff.mpr (eigenvector_maps_power q M G hMG μ v hv')
    · intro h0
      apply hv.2
      have h1 := hGinj 1
      rw [pow_one] at h1
      exact h1 (by rw [h0, map_zero])
  obtain ⟨z0, hz0⟩ := M.exists_eigenvalue
  have hall : ∀ i : ℕ, M.HasEigenvalue (z0 ^ q ^ i) := by
    intro i
    induction i with
    | zero => simpa using hz0
    | succ i ih =>
      have h := hstep _ ih
      rwa [← pow_mul, ← pow_succ] at h
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => z0 ^ q ^ i) (t := {μ | M.HasEigenvalue μ}) (fun i => hall i) hfin
  have hzE : M.HasEigenvalue (z0 ^ q ^ a) := hall a
  have hper : (z0 ^ q ^ a) ^ q ^ (b - a) = z0 ^ q ^ a := by
    rw [pow_pow_pow_add, show a + (b - a) = b by omega, ← heq]
  generalize z0 ^ q ^ a = z at hzE hper
  have hP : ∃ e : ℕ, 0 < e ∧ z ^ q ^ e = z := ⟨b - a, by omega, hper⟩
  obtain ⟨d, ⟨hd0, hzd⟩, hdmin⟩ : ∃ d : ℕ, (0 < d ∧ z ^ q ^ d = z) ∧
      ∀ e < d, ¬ (0 < e ∧ z ^ q ^ e = z) :=
    ⟨Nat.find hP, Nat.find_spec hP, fun e he => Nat.find_min hP he⟩

  have hmaps : ∀ x ∈ M.eigenspace z, (G ^ d) x ∈ M.eigenspace z := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [eigenvector_iterate_power q M G hMG z x hx d, hzd]
  have hne : M.eigenspace z ≠ ⊥ := hzE
  have : Nontrivial (M.eigenspace z) := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict (G ^ d) hmaps)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw1 : LinearMap.restrict (G ^ d) hmaps w = μ • w := Module.End.mem_eigenspace_iff.mp hw.1
  set v : V := (w : V) with hv_def
  have hGd : (G ^ d) v = μ • v := by
    have h := congrArg Subtype.val hw1
    simpa [LinearMap.restrict_apply] using h
  have hvE : M v = z • v := Module.End.mem_eigenspace_iff.mp w.2
  have hv0 : v ≠ 0 := by
    intro h
    apply hw.2
    exact Subtype.ext h

  let bb : Fin d → V := fun i => (G ^ (i : ℕ)) v
  have hb_eig : ∀ i : Fin d, M (bb i) = z ^ q ^ (i : ℕ) • bb i := fun i =>
    eigenvector_iterate_power q M G hMG z v hvE i
  have hb_ne : ∀ i : Fin d, bb i ≠ 0 := by
    intro i h
    apply hv0
    exact hGinj i (by rw [map_zero]; exact h)
  have key : ∀ i j : ℕ, i < j → j < d → z ^ q ^ i = z ^ q ^ j → False := by
    intro i j hij hjd hij'
    have h1 : z ^ q ^ (j - i) = z := by
      calc z ^ q ^ (j - i) = (z ^ q ^ d) ^ q ^ (j - i) := by rw [hzd]
        _ = (z ^ q ^ j) ^ q ^ (d - i) := by
          rw [pow_pow_pow_add, pow_pow_pow_add, show j + (d - i) = d + (j - i) by omega]
        _ = (z ^ q ^ i) ^ q ^ (d - i) := by rw [hij']
        _ = z ^ q ^ d := by rw [pow_pow_pow_add, show i + (d - i) = d by omega]
        _ = z := hzd
    exact hdmin (j - i) (by omega) ⟨by omega, h1⟩
  have hinj : Function.Injective (fun i : Fin d => z ^ q ^ (i : ℕ)) := by
    intro i j hij
    simp only at hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact (key i j h j.2 hij).elim
    · exact Fin.ext h
    · exact (key j i h i.2 hij.symm).elim
  have hli : LinearIndependent ℂ bb :=
    Module.End.eigenvectors_linearIndependent' M (fun i : Fin d => z ^ q ^ (i : ℕ)) hinj bb
      (fun i => ⟨Module.End.mem_eigenspace_iff.mpr (hb_eig i), hb_ne i⟩)
  set W : Submodule ℂ V := Submodule.span ℂ (Set.range bb) with hW_def
  have hvW : v ∈ W := Submodule.subset_span ⟨⟨0, hd0⟩, by simp [bb]⟩
  have hMW : ∀ x ∈ W, M x ∈ W := by
    have hle : W ≤ W.comap M := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hb_eig i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  have hGW : ∀ x ∈ W, G x ∈ W := by
    have hle : W ≤ W.comap G := by
      rw [hW_def, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show G ((G ^ (i : ℕ)) v) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ']
      by_cases h : (i : ℕ) + 1 < d
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, h⟩, rfl⟩
      · rw [show (i : ℕ) + 1 = d by omega, hGd]
        exact Submodule.smul_mem _ _ hvW
    exact fun x hx => hle hx
  have hWtop : W = ⊤ := by
    rcases hU W hMW hGW with h | h
    · exfalso
      apply hv0
      have := hvW
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exact h
  have hfr : Module.finrank ℂ V = d := by
    have h := finrank_span_eq_card hli
    rw [← hW_def, hWtop, finrank_top, Fintype.card_fin] at h
    exact h
  refine ⟨z, hzE, ?_⟩
  rw [hfr]
  refine ⟨?_, hzd, fun e he0 hed h => hdmin e hed ⟨he0, h⟩⟩
  intro hz
  apply hv0
  apply hMinj
  rw [hvE, hz, zero_smul, map_zero]

end PositivityTheory.Rg.DzCount

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace CentralCharacterTransfer

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  change (∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv h hh
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv h h.2

theorem map_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (H : Subgroup G) :
    (fixed ρ H).map φ.toLinearEquiv.toLinearMap = fixed σ H := by
  ext w
  simp only [Submodule.mem_map, mem_fixed_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ h hh
    change σ h (φ v) = φ v
    rw [← equiv_apply, hv h hh]
  · intro hw
    have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
    refine ⟨φ.toLinearEquiv.symm w, fun h hh => ?_, e2⟩
    apply φ.toLinearEquiv.injective
    change φ _ = φ _
    rw [equiv_apply, e2, hw h hh]

theorem hasCentralChar_of_equiv {k V W : Type} [Field k] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv σ)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := by
  intro z w
  have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
  rw [← e2, ← equiv_apply, h z]
  exact φ.toLinearEquiv.map_smul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {W W' V V' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} {τ' : Representation ℂ (GL (Fin n) 𝓀[k]) W'}
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) V'}
    {j : W →ₗ[ℂ] V} {j' : W' →ₗ[ℂ] V'} (hj : IsTypeMap τ π j) (hj' : IsTypeMap τ' π' j')
    (hf : fixed π (KOne k (Fin n)) = LinearMap.range j) (hf' : fixed π' (KOne k (Fin n)) = LinearMap.range j')
    (φ : π.Equiv π') : ∃ e : W ≃ₗ[ℂ] W', ∀ g v, e (τ g v) = τ' g (e v) := by
  have hm := map_fixed φ (KOne k (Fin n))
  rw [hf, hf'] at hm
  let e : W ≃ₗ[ℂ] W' := (LinearEquiv.ofInjective j hj.1).trans
    ((φ.toLinearEquiv.submoduleMap (LinearMap.range j)).trans
      ((LinearEquiv.ofEq _ _ hm).trans (LinearEquiv.ofInjective j' hj'.1).symm))
  have key : ∀ w, j' (e w) = φ (j w) := by
    intro w
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective j' hj'.1).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm) ((φ.toLinearEquiv.submoduleMap _) ((LinearEquiv.ofInjective j hj.1) w))))
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  refine ⟨e, fun g v => ?_⟩
  obtain ⟨g', rfl⟩ := GlobalTheory.LocGL.redK_surjective g
  apply hj'.1
  rw [key, hj.2, hj'.2, key]
  exact equiv_apply φ _ _

end CentralCharacterTransfer

open CentralCharacterTransfer in
theorem st8a : St4 → St5 → St6 → St7 → St8a := by
  classical
  intro h4 h5 h6 h7 k _ _ _ _ n hn ϖ hϖ c
  obtain ⟨τ, hτ, hinj⟩ := h7 𝓀[k] n hn
  have hdata : ∀ P ∈ Lab 𝓀[k] n, ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : (τ P).V →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap (τ P).ρ π.ρ j :=
    fun P hP => h4 k (τ P).V n hn (τ P).ρ (hτ P hP).1 ϖ hϖ c
  choose π ω j hω hc hj using hdata
  have hirr : (1 : Representation ℂ (GL (Fin n) k) ℂ).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun s => ?_ }
    · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
    · rcases Ideal.eq_bot_or_top s.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  let d : IrrRep (GL (Fin n) k) := ⟨ℂ, 1, fun v => by simp, hirr⟩
  let F : 𝓀[k][X] → IrrGL (k := k) := fun P =>
    if hP : P ∈ Lab 𝓀[k] n then ⟨n, Quotient.mk _ (π P hP)⟩ else ⟨n, Quotient.mk _ d⟩
  have hF : ∀ P (hP : P ∈ Lab 𝓀[k] n), F P = ⟨n, Quotient.mk _ (π P hP)⟩ := by
    intro P hP
    simp only [F, dif_pos hP]
  have hfix : ∀ P (hP : P ∈ Lab 𝓀[k] n),
      fixed (π P hP).ρ (KOne k (Fin n)) = LinearMap.range (j P hP) := by
    intro P hP
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    exact h6 k (τ P).V n (τ P).ρ (hτ P hP).2 (π P hP) (ω P hP) (hω P hP) (j P hP) (hj P hP)
  refine ⟨F, fun P hP => ?_, fun P hP P' hP' hPP => ?_⟩
  · haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    rw [hF P hP]
    obtain ⟨ψ⟩ : Nonempty ((π P hP).ρ.Equiv
        (IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).ρ) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).symm
    set π₀ := IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))
    let j₀ : (τ P).V →ₗ[ℂ] π₀.V := ψ.toLinearEquiv.toLinearMap ∘ₗ j P hP
    have hj₀ : IsTypeMap (τ P).ρ π₀.ρ j₀ := by
      refine ⟨ψ.toLinearEquiv.injective.comp (hj P hP).1, fun g v => ?_⟩
      change ψ (j P hP _) = π₀.ρ g (ψ (j P hP v))
      rw [(hj P hP).2, equiv_apply]
    have hcc := hasCentralChar_of_equiv ψ (hω P hP)
    refine ⟨rfl, ⟨hn, h5 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ j₀ hj₀⟩, ?_, ω P hP, hcc, hc P hP⟩
    change fixed π₀.ρ (KOne k (Fin n)) ≠ ⊥
    rw [h6 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ (ω P hP) hcc j₀ hj₀]
    obtain ⟨w, hw⟩ := exists_ne (0 : (τ P).V)
    intro hb
    apply hw
    apply hj₀.1
    rw [map_zero]
    have hm : j₀ w ∈ LinearMap.range j₀ := LinearMap.mem_range_self j₀ w
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rw [hF P hP, hF P' hP'] at hPP
    have hq := eq_of_heq (Sigma.mk.inj_iff.1 hPP).2
    obtain ⟨φ⟩ : Nonempty ((π P hP).ρ.Equiv (π P' hP').ρ) := Quotient.exact hq
    obtain ⟨e, he⟩ := transfer (hj P hP) (hj P' hP') (hfix P hP) (hfix P' hP') φ
    exact hinj P hP P' hP' ⟨e, he⟩

end PositivityTheory.Rg.DzCount

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

theorem lab_finite (K : Type) [Field K] [Finite K] (n : ℕ) : (Lab K n).Finite := by
  have h : Finite (Polynomial.degreeLT K (n + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv K (n + 1)).symm.toEquiv
  refine Set.Finite.subset (Set.toFinite ((Polynomial.degreeLT K (n + 1) : Submodule K K[X]) : Set K[X])) fun P hP => ?_
  refine Polynomial.mem_degreeLT.2 (lt_of_le_of_lt Polynomial.degree_le_natDegree ?_)
  rw [hP.2.2.2]
  exact_mod_cast Nat.lt_succ_self n

end PositivityTheory.Rg.DzCount

end
end
