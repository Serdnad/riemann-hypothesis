module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsInducedIntPrimeTo
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle011
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.SimpleModule.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle013
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
public import Mathlib.LinearAlgebra.PID
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.BlockTheory.IrreducibleCharacters.CuspidalCharacters
import Formalism.UnipotentAdelicQuotients.Bundle001
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

private theorem trace_block_permutation (K : Type) [Field K] (X : Type) [Fintype X] [DecidableEq X]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (π : X → X)
    (A : X → W →ₗ[K] W) :
    LinearMap.trace K (X → W) (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q))
      = ∑ q, if π q = q then LinearMap.trace K W (A q) else 0 := by
  have hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W))
      = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q)) := by
    apply LinearMap.ext
    intro f
    funext p
    simp

  rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · have hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hid, LinearMap.comp_id]
  · have hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0 := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hz, LinearMap.comp_zero, map_zero]

section
variable {G : Type} [Group G] (H : Subgroup G)

theorem cosetCocycle_mem (g : G) (q : G ⧸ H) : q.out⁻¹ * g * (g⁻¹ • q).out ∈ H := by
  have h : ((g⁻¹ * q.out : G) : G ⧸ H) = (((g⁻¹ • q).out : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  have hm := QuotientGroup.eq.mp h
  simpa [mul_assoc] using hm

def cosetCocycle (g : G) (q : G ⧸ H) : H := ⟨_, cosetCocycle_mem H g q⟩

theorem cosetCocycle_one (q : G ⧸ H) : cosetCocycle H 1 q = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

theorem cosetCocycle_mul (a b : G) (q : G ⧸ H) :
    cosetCocycle H (a * b) q = cosetCocycle H a q * cosetCocycle H b (a⁻¹ • q) := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul]
  rw [mul_inv_rev, mul_smul]
  group

theorem inv_smul_eq_iff_conj_mem (g : G) (q : G ⧸ H) :
    g⁻¹ • q = q ↔ q.out⁻¹ * g * q.out ∈ H := by
  have hs : g⁻¹ • q = ((g⁻¹ * q.out : G) : G ⧸ H) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  calc g⁻¹ • q = q ↔ ((g⁻¹ * q.out : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) := by
        rw [hs, QuotientGroup.out_eq']
    _ ↔ q.out⁻¹ * g * q.out ∈ H := by
        rw [QuotientGroup.eq]
        simp [mul_assoc]

def cosetIndRep {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : Representation K H W) :
    Representation K G (G ⧸ H → W) where
  toFun g := LinearMap.pi fun q => σ (cosetCocycle H g q) ∘ₗ LinearMap.proj (g⁻¹ • q)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro f
    funext q
    simp [cosetCocycle_mul, mul_smul]
end

theorem isChar_finsum_conj_ext0_of_isChar :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  intro K L _ _ _ G _ _ H ψ hψ
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨n, σ, hσ⟩ := hψ
  obtain ⟨m, ρ, hρ⟩ :=
    (isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1
  refine ⟨m, ρ, fun g => ?_⟩
  have hg := hρ g
  simp only at hg
  rw [← hg]
  show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _
  have hc : (cosetIndRep H σ).character g
      = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0 :=
    trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q)
      (fun q => σ (cosetCocycle H g q))

  rw [finsum_eq_sum_of_fintype, hc, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g⁻¹ • q = q
  · have hm : q.out⁻¹ * g * q.out ∈ H := (inv_smul_eq_iff_conj_mem H g q).mp h
    have he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q :=
      Subtype.ext (by simp [cosetCocycle, h])
    rw [if_pos h, ext0, dite_eq_left hm, hσ, he]
    rfl
  · have hm : q.out⁻¹ * g * q.out ∉ H := fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)
    rw [if_neg h, ext0, dite_eq_right hm, map_zero]

end GlobalTheory.BI
end
end

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_trace_mul_idempotent :
    ∀ (L : Type) [Field L] (T : Type) [Group T] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L T V) (e : Module.End L V), e * e = e → (∀ t, ρ t * e = e * ρ t) → _root_.GlobalTheory.BI.IsChar L L (fun t => LinearMap.trace L V (ρ t * e)) := by
  intro L _ T _ V _ _ _ ρ e he hc
  have hfix : ∀ v ∈ LinearMap.range e, e v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, he]
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range e, fun t v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1
  convert key using 2 with t
  rw [Algebra.algebraMap_self, RingHom.id_apply, Representation.character,
    ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e)
      (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]
  congr 1
  ext ⟨v, hv⟩
  change (ρ t * e) v = ρ t v
  rw [Module.End.mul_apply, hfix v hv]

end GlobalTheory.BI
end
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by
  first | exact @GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | exact GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | (intros; apply GlobalTheory.BI.pair_self_of_isIrrChar_algClosed <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  first | exact @GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | (intros; apply GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex : ∀ (G : Type) [Group G] (χ : G → ℂ), (∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)) ↔ IsChar ℂ ℂ χ := by
  first | exact @GlobalTheory.BI.matrixChar_iff_isChar | exact GlobalTheory.BI.matrixChar_iff_isChar | (intros; apply GlobalTheory.BI.matrixChar_iff_isChar <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ (E : Subgroup G) (f : G → ℤ) (ι : Type) (_ : Fintype ι) (r : ι → ℂ) (lam : ι → E →* ℂˣ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ¬ (p : ℤ) ∣ f x ∧ (∀ i, IsIntegral ℤ (r i)) ∧ ∀ g, (f g : ℂ) = ∑ i, r i * ind E (fun e => (lam i e : ℂ)) g := by
  first | exact @GlobalTheory.exists_induced_int_prime_to | exact GlobalTheory.exists_induced_int_prime_to | (intros; apply GlobalTheory.exists_induced_int_prime_to <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem invariant_eq_top_of_irreducible {k : Type} [Field k] {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ρ.IsIrreducible)
    (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    U = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation ρ) with H | H
  · have H' : U = ⊥ := congrArg Subrepresentation.toSubmodule H
    exact absurd (by simpa [H'] using hv) hv0
  · exact congrArg Subrepresentation.toSubmodule H

theorem finrank_eq_one_or_imprimitive : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → ρ.IsIrreducible → Module.finrank k V = 1 ∨ ∃ (T : Subgroup G) (W : Submodule k V), T ≠ ⊤ ∧ (∀ t ∈ T, ∀ w ∈ W, ρ t w ∈ W) ∧ iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)) ∧ ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤ := by
  intro k _ G _ _ V _ _ _ ρ _ hG hirr
  haveI : Nontrivial V := by
    have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    have h2 : (⊥ : Submodule k V) ≠ ⊤ := fun H => h1 (Subrepresentation.ext H)
    exact (Submodule.nontrivial_iff k).1 ⟨_, _, h2⟩
  by_cases hc : ∀ a b : G, ρ a * ρ b = ρ b * ρ a
  · left
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun g : G => ρ g) hc
    have htop := invariant_eq_top_of_irreducible ρ hirr (Submodule.span k {v}) (by
      intro g w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨m, hm⟩ := hv g
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hm' : ρ g v = m • v := hm
      rw [hm']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      v (Submodule.mem_span_singleton_self v) hv0
    rw [← finrank_top, ← htop, finrank_span_singleton hv0]
  right
  have hB : ¬ ∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) →
      ∀ b ∈ B, ∀ g : G, ρ b * ρ g = ρ g * ρ b := fun H => hc (commute_all G _ ρ hG H)
  push Not at hB
  obtain ⟨B, hBn, hBc, b₀, hb₀, g₀, hne⟩ := hB
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.exists_common_eigenvector_of_commute (fun b : B => ρ b)
    (fun a b => hBc a a.2 b b.2)
  choose μ hμ using hv
  let c : G →* MulAut B := MulAut.conjNormal
  have hcv : ∀ (g : G) (b : B), ((c g b : B) : G) = g * b * g⁻¹ := fun g b => rfl
  let E : (B → k) → Submodule k V := fun χ => ⨅ b : B, Module.End.eigenspace (ρ b) (χ b)
  have hE : ∀ χ w, w ∈ E χ ↔ ∀ b : B, ρ b w = χ b • w := by
    intro χ w
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hind : iSupIndep E :=
    (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun b : B => ρ b)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hBc j j.2 i i.2) φ).mono fun _ =>
        iInf_mono fun i => (Module.End.genEigenspace (ρ i) _).monotone le_top
  have hmap : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ E (fun b => μ (c g⁻¹ b)) := by
    intro g w hw
    rw [hE] at hw ⊢
    intro b
    rw [← map_smul, ← hw, hcv, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
      ← map_mul]
    congr 2
    group
  let T : Subgroup G :=
    { carrier := {g | ∀ b, μ (c g b) = μ b}
      one_mem' := fun b => by simp
      mul_mem' := fun {x y} hx hy b => by
        rw [map_mul, MulAut.mul_apply, hx, hy]
      inv_mem' := fun {x} hx b => by
        rw [← hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] }
  have hT : ∀ g, g ∈ T ↔ ∀ b, μ (c g b) = μ b := fun g => Iff.rfl
  have hstab : ∀ t ∈ T, ∀ w ∈ E μ, ρ t w ∈ E μ := by
    intro t ht w hw
    have h1 := hmap t w hw
    have h2 : (fun b => μ (c t⁻¹ b)) = μ := funext ((hT _).1 (T.inv_mem ht))
    rwa [h2] at h1
  have hvE : v ∈ E μ := (hE _ _).2 hμ
  refine ⟨T, E μ, ?_, hstab, ?_, ?_⟩
  · intro hTop
    have htop := invariant_eq_top_of_irreducible ρ hirr (E μ)
      (fun g w hw => hstab g (hTop ▸ Subgroup.mem_top g) w hw) v hvE hv0
    have hs : ∀ w, ρ b₀ w = μ ⟨b₀, hb₀⟩ • w := fun w =>
      (hE μ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
    apply hne
    ext w
    simp only [Module.End.mul_apply, hs, map_smul]
  · have hinj : Function.Injective fun q : G ⧸ T => fun b => μ (c q.out⁻¹ b) := by
      intro q q' hq
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 ((hT _).2 fun b => ?_)
      have h1 : μ (c q.out⁻¹ (c q'.out b)) = μ (c q'.out⁻¹ (c q'.out b)) := congrFun hq _
      rw [map_mul, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply]
    refine (hind.comp hinj).mono fun q => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hmap _ w hw
  · have hmem : ∀ (g : G) (w : V), w ∈ E μ → ρ g w ∈ ⨆ q : G ⧸ T, (E μ).map (ρ q.out) := by
      intro g w hw
      obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T g
      refine Submodule.mem_iSup_of_mem (g : G ⧸ T) ⟨ρ (t⁻¹ : G) w, hstab _ (T.inv_mem t.2) w hw, ?_⟩
      rw [ht, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine invariant_eq_top_of_irreducible ρ hirr _ ?_ v (by simpa using hmem 1 v hvE) hv0
    intro g w hw
    have hle : (⨆ q : G ⧸ T, (E μ).map (ρ q.out)) ≤
        (⨆ q : G ⧸ T, (E μ).map (ρ q.out)).comap (ρ g) := by
      refine iSup_le fun q => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact hmem _ u hu
    exact hle hw

end GlobalTheory.BI
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  first | exact @GlobalTheory.BI.isChar_linear | exact GlobalTheory.BI.isChar_linear | (intros; apply GlobalTheory.BI.isChar_linear <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ), (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) → ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  first | exact @GlobalTheory.exists_equiv_of_sum_min_eq | exact GlobalTheory.exists_equiv_of_sum_min_eq | (intros; apply GlobalTheory.exists_equiv_of_sum_min_eq <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by
  first | exact @GlobalTheory.CuspGL.primary_structure | exact GlobalTheory.CuspGL.primary_structure | (intros; apply GlobalTheory.CuspGL.primary_structure <;> assumption)
end

section

namespace GlobalTheory.CuspCharCompare

open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra

section Group

variable {G : Type} [Group G]

theorem isSimpleModule_of_finrank_end {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] [SMulCommClass R ℂ M] [IsSemisimpleModule R M]
    (h : Module.finrank ℂ (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

variable [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end Group

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end GlobalTheory.CuspCharCompare
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V), ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, (Nat.card {v : W.1 // ∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ) = (Nat.card F : ℂ) ^ Module.finrank F V := by
  first | exact @GlobalTheory.CuspGL.finsum_card_cyclic_eq | exact GlobalTheory.CuspGL.finsum_card_cyclic_eq | (intros; apply GlobalTheory.CuspGL.finsum_card_cyclic_eq <;> assumption)
end
