module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle506
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin GlobalTheory.BCWords

namespace PositivityTheory.Rg.Rs.PInfInd2A

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem exists_scalar {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Zalg E N) (hc : ∀ o : Op E N, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E N) => z φ) '' Zalg E N) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_hasInfCharGL {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (τ : E →+* ℂ) :
    ∃ m, HasInfCharGL V τ m := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := N) τ) (((N : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_scalar hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

def blkV {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1))) :
    ∀ i : Fin 2, Submodule ℂ (Sm E (n i))
  | ⟨0, _⟩ => W₁
  | ⟨1, _⟩ => W₂

def blkE {n : Fin 2 → ℕ} {W₁ : Submodule ℂ (Sm E (n 0))} {W₂ : Submodule ℂ (Sm E (n 1))} (φ₁ : W₁) (φ₂ : W₂) :
    ∀ i : Fin 2, blkV W₁ W₂ i
  | ⟨0, _⟩ => φ₁
  | ⟨1, _⟩ => φ₂

theorem levPair_eta {R : Type} [CommRing R] {n : Fin 2 → ℕ} (m : ∀ i : Fin 2, GL (Fin (n i)) R) :
    CapFactor.levPair (m 0, m 1) = m := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem tensorSp_of_tens2 {n : Fin 2 → ℕ} (W₁ : Submodule ℂ (Sm E (n 0))) (W₂ : Submodule ℂ (Sm E (n 1)))
    {T : GA E (n 0) × GA E (n 1) → ℂ} (hT : T ∈ tens2 W₁ W₂) :
    (fun m : ∀ i, GA E (n i) => T (m 0, m 1)) ∈ tensorSp (blkV W₁ W₂) := by
  let L : (GA E (n 0) × GA E (n 1) → ℂ) →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
    { toFun := fun F m => F (m 0, m 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tens2 W₁ W₂ ≤ (tensorSp (blkV W₁ W₂)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    refine Submodule.subset_span ⟨blkE ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩, ?_⟩
    funext m
    change φ₁.1 (m 0) * φ₂.1 (m 1) = ∏ i : Fin 2, ((blkE (W₁ := W₁) (W₂ := W₂) ⟨φ₁, h₁⟩ ⟨φ₂, h₂⟩ i).1).1 (m i)
    rw [Fin.prod_univ_two]
    rfl
  exact hle hT

end PositivityTheory.Rg.Rs.PInfInd2A

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {R : Type} [CommRing R] {a d₁ d₂ r s : ℕ}

theorem val_stdBlocks_const {d N : ℕ} (h : ∑ _ : Fin d, a = N) (b : Fin d) (i : Fin a) :
    ((stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩ : Fin N) : ℕ) = (b : ℕ) * a + i := by
  rw [stdBlocks_val]
  simp

theorem sum_const_eq {d N : ℕ} (h : ∑ _ : Fin d, a = N) : N = d * a := by
  rw [← h]
  simp

theorem stdBlocks_castAdd (h₁ : ∑ _ : Fin d₁, a = r) (H : ∑ _ : Fin (d₁ + d₂), a = r + s) (b : Fin d₁) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.castAdd d₂ b, i⟩ = Fin.castAdd s (stdBlocks (fun _ : Fin d₁ => a) h₁ ⟨b, i⟩) := by
  apply Fin.ext
  rw [val_stdBlocks_const, Fin.coe_castAdd, Fin.coe_castAdd, val_stdBlocks_const]

theorem stdBlocks_natAdd (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (b : Fin d₂) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.natAdd d₁ b, i⟩ = Fin.natAdd r (stdBlocks (fun _ : Fin d₂ => a) h₂ ⟨b, i⟩) := by
  apply Fin.ext
  simp only [val_stdBlocks_const, Fin.val_natAdd, sum_const_eq h₁]
  ring

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) i (Fin.castAdd s k) = _
  rw [Matrix.add_apply]
  have h0 : nilM x i (Fin.castAdd s k) = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_castAdd]
    rw [dite_eq_right]
    intro h
    exact absurd h.2 (not_le.2 k.isLt)
  rw [h0, add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) (Fin.natAdd r k) j = _
  rw [Matrix.add_apply]
  have h0 : nilM x (Fin.natAdd r k) j = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_natAdd]
    rw [dite_eq_right]
    intro h
    omega
  rw [h0, add_zero]

theorem unip_lev_cc (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add, unip_col, lev_nc, lev_cc, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, Fin.castAdd_inj, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem unip_lev_nn (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, unip_row]
  rw [← Matrix.mul_apply, Matrix.one_mul, lev_nn]

theorem castAdd_or_natAdd (b : Fin (d₁ + d₂)) : (∃ c, b = Fin.castAdd d₂ c) ∨ ∃ c, b = Fin.natAdd d₁ c := by
  rcases lt_or_ge (b : ℕ) d₁ with h | h
  · exact Or.inl ⟨⟨b, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨b - d₁, by omega⟩, Fin.ext ?_⟩
    simp only [Fin.coe_natAdd]
    omega

theorem leviEmb_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (m : ∀ _ : Fin (d₁ + d₂), GL (Fin a) R) :
    leviEmb R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m =
      lev R r s (leviEmb R (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b)),
        leviEmb R (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b))) := by
  have hcn : ∀ (c : Fin d₁) (c' : Fin d₂), Fin.castAdd d₂ c ≠ Fin.natAdd d₁ c' := by
    intro c c' h
    have h1 := congrArg Fin.val h
    have h2 := c.isLt
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  apply Units.ext
  ext p q
  obtain ⟨⟨b, i⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective p
  obtain ⟨⟨b', j⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective q
  rcases castAdd_or_natAdd b with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    rcases castAdd_or_natAdd b' with ⟨c', rfl⟩ | ⟨c', rfl⟩
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_castAdd h₁ H, stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.castAdd_injective _ _ h)), stdBlocks_castAdd h₁ H,
        stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_ne R _ _ hc]
  · rw [leviEmb_apply_ne R _ _ (hcn c c'), stdBlocks_castAdd h₁ H, stdBlocks_natAdd h₁ h₂ H, lev_cn]
  · rw [leviEmb_apply_ne R _ _ (fun h => hcn c' c h.symm), stdBlocks_natAdd h₁ h₂ H,
      stdBlocks_castAdd h₁ H, lev_nc]
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_natAdd h₁ h₂ H, stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.natAdd_injective _ _ h)), stdBlocks_natAdd h₁ h₂ H,
        stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_ne R _ _ hc]

theorem unipRad_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {v : GL (Fin (r + s)) R} (hv : v ∈ unipRad R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H)) :
    ∃ (x : BlockIx (r + s) r → R) (v₁ : GL (Fin r) R) (v₂ : GL (Fin s) R),
      v₁ ∈ unipRad R (stdBlocks (fun _ : Fin d₁ => a) h₁) ∧ v₂ ∈ unipRad R (stdBlocks (fun _ : Fin d₂ => a) h₂) ∧
      v = unip x * lev R r s (v₁, v₂) := by
  have low : ∀ g : GL (Fin (r + s)) R, g ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix _ _ R) i j = 0 := by
    intro g hg i j hi hj
    rw [mem_parab_iff] at hg
    have hi' := i.isLt
    obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd r i' :=
      ⟨⟨i - r, by omega⟩, Fin.ext (by simp only [Fin.coe_natAdd]; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd s j' := ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨⟨c, i''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₂ => a) h₂).surjective i'
    obtain ⟨⟨c', j''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₁ => a) h₁).surjective j'
    rw [← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_castAdd h₁ H]
    apply hg
    have := c'.isLt
    rw [Fin.lt_def]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  obtain ⟨hvP, hvD⟩ := mem_unipRad.1 hv
  have hvP' := mem_parab_iff.1 hvP
  have hinvP : v⁻¹ ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) :=
    (mem_unipRad.1 ((unipRad R _).inv_mem hv)).1
  obtain ⟨x, m, hvm⟩ := GlobalTheory.CompanionTheory.CTFin.IwaFin.exists_unip_mul_lev r s v (low v hvP) (low v⁻¹ hinvP)
  refine ⟨x, m.1, m.2, ?_, ?_, hvm⟩
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simpa only [Fin.coe_castAdd] using hβα
    · intro α i j
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      exact hvD _ _ _
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simp only [Fin.coe_natAdd]
      omega
    · intro α i j
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      exact hvD _ _ _

end PositivityTheory.Rg.Rs.InductionInStages

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def cf (a : ℕ) (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

theorem A.act_cf {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (ψ : Sm E a) (x : GA E a) :
    (act (.cpt k) (act (.fin g) ψ)).1 x = ψ.1 (x * cf a k g) := congrArg ψ.1 (mul_assoc _ _ _)

theorem A.sum_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ U₁) (h₂ : ∀ i, ψ₂ i ∈ U₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 U₁ U₂ := by
  have := Submodule.sum_mem (tens2 U₁ U₂) (t := Finset.univ)
    (f := fun i (m : GA E r × GA E s) => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2)
    fun i _ => Submodule.subset_span ⟨_, h₁ i, _, h₂ i, rfl⟩
  convert this using 1
  funext m
  simp

theorem exists_extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) :
    ∃ T : Module.End ℂ (GA E a → ℂ), ∀ ψ : Sm E a, T ψ.1 = (f ψ).1 := by
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Sm E a).subtype ∘ₗ f)
  exact ⟨T, fun ψ => LinearMap.congr_fun hT ψ⟩

def extOp {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) : Module.End ℂ (GA E a → ℂ) := (exists_extOp f).choose

theorem extOp_apply {a : ℕ} (f : Sm E a →ₗ[ℂ] Sm E a) (ψ : Sm E a) : extOp f ψ.1 = (f ψ).1 :=
  (exists_extOp f).choose_spec ψ

def tensOp (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) : Module.End ℂ (GA E r × GA E s → ℂ) where
  toFun F m := extOp f₂ (fun b => extOp f₁ (fun a => F (a, b)) m.1) m.2
  map_add' F G := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (F + G) (a, b)) m.1) =
        (fun b => extOp f₁ (fun a => F (a, b)) m.1) + fun b => extOp f₁ (fun a => G (a, b)) m.1 :=
      funext fun b => congrFun (map_add (extOp f₁) (fun a => F (a, b)) fun a => G (a, b)) m.1
    rw [e, map_add (f := _)]
    rfl
  map_smul' c F := by
    funext m
    have e : (fun b => extOp f₁ (fun a => (c • F) (a, b)) m.1) = c • fun b => extOp f₁ (fun a => F (a, b)) m.1 :=
      funext fun b => congrFun (map_smul (extOp f₁) c fun a => F (a, b)) m.1
    rw [e, map_smul]
    rfl

theorem tensOp_sum (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {n : ℕ} (ψ₁ : Fin n → Sm E r)
    (ψ₂ : Fin n → Sm E s) :
    tensOp f₁ f₂ (fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) = fun m => ∑ i, (f₁ (ψ₁ i)).1 m.1 * (f₂ (ψ₂ i)).1 m.2 := by
  funext m
  have e1 : ∀ b, (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) = ∑ i, (ψ₂ i).1 b • (ψ₁ i).1 := fun b => by
    funext a; simp [mul_comm]
  have e2 : (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) = ∑ i, (f₁ (ψ₁ i)).1 m.1 • (ψ₂ i).1 := by
    funext b

    rw [e1, map_sum]
    simp [extOp_apply, mul_comm]
  change extOp f₂ (fun b => extOp f₁ (fun a => ∑ i, (ψ₁ i).1 a * (ψ₂ i).1 b) m.1) m.2 = _

  rw [e2, map_sum]
  simp [extOp_apply]

theorem tensor_pair_finite_sum {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ U₁) ∧ (∀ i, ψ₂ i ∈ U₂) ∧
      F = fun m => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hF
  choose φ₁ h₁ φ₂ h₂ e using fun i => (g i).2
  refine ⟨n, fun i => c i • φ₁ i, φ₂, fun i => U₁.smul_mem _ (h₁ i), h₂, funext fun m => ?_⟩
  simp [e, mul_assoc]

theorem tensOp_id {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 U₁ U₂) : tensOp LinearMap.id LinearMap.id F = F := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  rfl

theorem tensOp_mem (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s) {U₁ : Submodule ℂ (Sm E r)}
    {U₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) : tensOp f₁ f₂ F ∈ tens2 ⊤ ⊤ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  rw [tensOp_sum]
  exact A.sum_mem (fun _ => trivial) fun _ => trivial

theorem tensOp_translate {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} (hU₁ : _root_.GlobalTheory.CuspRep.IsStable U₁)
    (hU₂ : _root_.GlobalTheory.CuspRep.IsStable U₂) {f₁ : Sm E r →ₗ[ℂ] Sm E r} {f₂ : Sm E s →ₗ[ℂ] Sm E s}
    (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)) (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ))
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s)
    (g₂ : GL (Fin s) (Af E)) :
    tensOp f₁ f₂ (fun m => F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂)) =
      fun m => tensOp f₁ f₂ F (m.1 * cf r k₁ g₁, m.2 * cf s k₂ g₂) := by
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hF
  have e := tensOp_sum f₁ f₂ (fun i => act (.cpt k₁) (act (.fin g₁) (ψ₁ i))) fun i => act (.cpt k₂) (act (.fin g₂) (ψ₂ i))
  simp only [A.act_cf] at e
  rw [e, tensOp_sum]
  funext m
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf₁ _ _ (hU₁ _ _ (h₁ i)), hf₁ _ _ (h₁ i), hf₂ _ _ (hU₂ _ _ (h₂ i)), hf₂ _ _ (h₂ i), A.act_cf, A.act_cf]

theorem tensOp_deriv {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {f₁ : Sm E r →ₗ[ℂ] Sm E r}
    {f₂ : Sm E s →ₗ[ℂ] Sm E s} (hf₁ : ∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ))
    (hf₂ : ∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)) (γ₁ : ℝ → GL (Fin r) (Cinf E)) (γ₂ : ℝ → GL (Fin s) (Cinf E))
    (Z₁ : Lie E r) (Z₂ : Lie E s) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1) (hγ₁ : HasDerivAt (fun t => toL (γ₁ t).val) Z₁ 0)
    (hγ₂ : HasDerivAt (fun t => toL (γ₂ t).val) Z₂ 0) {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) :
    ∃ G : GA E r × GA E s → ℂ,
      (∀ m, HasDerivAt (fun t => F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (G m) 0) ∧
      ∀ m, HasDerivAt (fun t => tensOp f₁ f₂ F (m.1 * infGL E r (γ₁ t), m.2 * infGL E s (γ₂ t))) (tensOp f₁ f₂ G m) 0 := by
  obtain ⟨n, ψ₁, ψ₂, u₁, u₂, rfl⟩ := tensor_pair_finite_sum hF
  have key : ∀ (χ₁ : Fin n → Sm E r) (χ₂ : Fin n → Sm E s) (m : GA E r × GA E s),
      HasDerivAt (fun t => ∑ i, (χ₁ i).1 (m.1 * infGL E r (γ₁ t)) * (χ₂ i).1 (m.2 * infGL E s (γ₂ t)))
        (∑ i, (lie E r Z₁ (χ₁ i)).1 m.1 * (χ₂ i).1 m.2 + ∑ i, (χ₁ i).1 m.1 * (lie E s Z₂ (χ₂ i)).1 m.2) 0 := by
    intro χ₁ χ₂ m
    rw [← Finset.sum_add_distrib]
    refine HasDerivAt.fun_sum fun i _ => ?_
    have := (hasDerivAt_curve (χ₁ i) m.1 γ₁ Z₁ h₁ hγ₁).mul (hasDerivAt_curve (χ₂ i) m.2 γ₂ Z₂ h₂ hγ₂)
    simp only [h₁, h₂, map_one, mul_one] at this
    exact this
  refine ⟨(fun m => ∑ i, (lie E r Z₁ (ψ₁ i)).1 m.1 * (ψ₂ i).1 m.2) + fun m => ∑ i, (ψ₁ i).1 m.1 * (lie E s Z₂ (ψ₂ i)).1 m.2,
    key ψ₁ ψ₂, fun m => ?_⟩
  rw [map_add (f := _), tensOp_sum, tensOp_sum, tensOp_sum]
  have e₁ : ∀ i, f₁ (lie E r Z₁ (ψ₁ i)) = lie E r Z₁ (f₁ (ψ₁ i)) := fun i => hf₁ (.lie Z₁) _ (u₁ i)
  have e₂ : ∀ i, f₂ (lie E s Z₂ (ψ₂ i)) = lie E s Z₂ (f₂ (ψ₂ i)) := fun i => hf₂ (.lie Z₂) _ (u₂ i)
  simp only [e₁, e₂]
  exact key (fun i => f₁ (ψ₁ i)) (fun i => f₂ (ψ₂ i)) m

theorem contDiffAt_tens {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {y₀ : P} (b₁ : P → GL (Fin r) (Cinf E)) (b₂ : P → GL (Fin s) (Cinf E))
    (hb₁ : ContDiffAt ℝ ∞ (fun y => toL (b₁ y).val) y₀) (hb₂ : ContDiffAt ℝ ∞ (fun y => toL (b₂ y).val) y₀)
    {F : GA E r × GA E s → ℂ} (hF : F ∈ tens2 U₁ U₂) (m : GA E r × GA E s) :
    ContDiffAt ℝ ∞ (fun y => F (m.1 * infGL E r (b₁ y), m.2 * infGL E s (b₂ y))) y₀ := by
  obtain ⟨n, ψ₁, ψ₂, -, -, rfl⟩ := tensor_pair_finite_sum hF
  refine ContDiffAt.sum fun i _ => ContDiffAt.mul ?_ ?_
  · have := (contDiffAt_chart (ψ₁ i).2 m.1 (val_mem_invSet (b₁ y₀))).comp y₀ hb₁
    simpa only [Function.comp_def, chart_val] using this
  · have := (contDiffAt_chart (ψ₂ i).2 m.2 (val_mem_invSet (b₂ y₀))).comp y₀ hb₂
    simpa only [Function.comp_def, chart_val] using this

end PositivityTheory.Rg.Rs.InducedTensorMap

end
end
