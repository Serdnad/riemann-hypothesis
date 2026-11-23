module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.CptRepMemTypePart
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.IntegrableDescendSupP
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle590
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapD
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle006
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapA

@[expose] public section

section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open Leaf2Aux in
theorem leaf_holds2 : Leaf :=
  leaf_of (core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Eig {a : ℕ} (L : Submodule ℂ (Sm E a)) (σ : (E →+* ℂ) → Multiset ℂ) (sh : ℂ) : Submodule ℂ (Sm E a) where
  carrier := {φ | φ ∈ L ∧ ∀ τ w, cap τ w φ = ((σ τ).map (fun z => w + sh + z)).prod • φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨L.add_mem hφ.1 hψ.1, fun τ w => by rw [map_add (f := _), hφ.2, hψ.2, smul_add]⟩
  zero_mem' := ⟨L.zero_mem, fun τ w => by rw [map_zero, smul_zero]⟩
  smul_mem' := fun c φ hφ => ⟨L.smul_mem c hφ.1, fun τ w => by rw [map_smul, hφ.2, smul_comm]⟩

def adm (mm : (E →+* ℂ) → Multiset ℂ) (n : ℕ) : Finset ((E →+* ℂ) → Multiset ℂ) := by
  classical
  exact Fintype.piFinset fun τ => ((mm τ).powerset.filter fun σ => Multiset.card σ = n).toFinset

theorem mem_adm {mm : (E →+* ℂ) → Multiset ℂ} {n : ℕ} {σ : (E →+* ℂ) → Multiset ℂ} :
    σ ∈ adm mm n ↔ ∀ τ, σ τ ≤ mm τ ∧ Multiset.card (σ τ) = n := by
  classical
  unfold adm
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun τ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter, Multiset.mem_powerset]

variable {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem LS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E r, ∀ φ ∈ LS U T, z φ ∈ LS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.LS_stable hU hT (.lie X)) hz φ hφ

theorem RS_zalg (hU : IsAutSt U) (hT : IsSliceMap U c T) : ∀ z ∈ Zalg E s, ∀ φ ∈ RS U T, z φ ∈ RS U T :=
  fun _ hz φ hφ => Zalg_stable (fun X => BlockSlices.RS_stable hU hT (.lie X)) hz φ hφ

theorem data_one (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    (∀ τ u, cap τ u (T ψ) = ((mm τ).map (u + ·)).prod • T ψ) ∧
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s), (∀ i, b i ∈ LS U T) ∧ (∀ i, q i ∈ RS U T) ∧
      ∀ p, (T ψ).1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  refine ⟨fun τ u => ?_, ?_⟩
  · have hI : ∀ X, ∀ φ ∈ U, lie E (r + s) X φ ∈ U := fun X φ hφ => hU.1 (.lie X) φ hφ
    rw [← (BlockSlices.zalg_comm hI T hT.equiv (cap_mem_Zalg τ u) ψ hψ).2, (hinf τ).2 u ψ hψ, map_smul]
  · obtain ⟨n, b, q, hb, hq, he⟩ := BlockSlices.expand hU hT ψ hψ 1 1
    refine ⟨n, b, q, fun i => ?_, fun i => rsF_sub_RS hψ 1 1 (hq i), fun p => ?_⟩
    · exact (Submodule.span_le.2 (lsF_sub_LS hψ 1 1)) (hb i)
    · rw [← he p, BlockSlices.yp_one, mul_one]

theorem LS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    LS U T ≤ ⨆ σ ∈ adm mm r, Eig (LS U T) σ ((s : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le b hb (LS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.1 m₂
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₁ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₁
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : σ.1 ∈ adm mm r := mem_adm.2 (hS σ.1 σ.2).1
  exact Submodule.mem_iSup_of_mem σ.1 (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), hθe σ.1 σ.2⟩)

theorem RS_le_iSup (hU : IsAutSt U) (hT : IsSliceMap U c T) (mm : (E →+* ℂ) → Multiset ℂ) (hmm : ∀ τ, (mm τ).Nodup)
    (hinf : ∀ τ, HasInfCharGL U τ (mm τ)) :
    RS U T ≤ ⨆ ρ ∈ adm mm s, Eig (RS U T) ρ (-(r : ℂ) / 2) := by
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩
  obtain ⟨ψ', hψ', e⟩ := BlockSlices.base_one hU hT hψ k g
  obtain ⟨hcap, n, b, q, hb, hq, hG⟩ := data_one hU hT mm hinf hψ'
  obtain ⟨S, x, hsum, hS⟩ := decomp_G (T ψ') (hT.unipInv ψ' hψ') mm hmm hcap b q
    (fun i => BlockSlices.LS_aut hT _ (hb i)) (fun i => BlockSlices.RS_aut hT _ (hq i)) hG
  have hz := zspan_le q hq (RS_zalg hU hT)
  choose θ hθ hθx hθe using fun σ (hσ : σ ∈ S) => (hS σ hσ).2.2 m₁
  have hℓ' : ℓ = ∑ σ ∈ S.attach, θ σ.1 σ.2 := by
    refine Subtype.ext (funext fun m₂ => ?_)
    rw [hℓ, ← e, hsum, Submodule.coe_sum, Finset.sum_apply, ← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun σ _ => hθx σ.1 σ.2 m₂
  rw [SetLike.mem_coe, hℓ']
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hadm : (fun τ => mm τ - σ.1 τ) ∈ adm mm s := mem_adm.2 fun τ => by
    refine ⟨Multiset.sub_le_self _ _, ?_⟩
    rw [Multiset.card_sub ((hS σ.1 σ.2).1 τ).1, (hinf τ).1, ((hS σ.1 σ.2).1 τ).2]
    omega
  refine Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hadm ⟨hz (hθ σ.1 σ.2), fun τ w => ?_⟩)
  rw [hθe σ.1 σ.2 τ w]
  congr 3
  funext z
  ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
end

section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

theorem d_pos : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this

theorem LS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ r', 0 < r' → r' < r → ∀ c' ∈ Exp r' φ.1,
      c'.re ≤ (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 := by
  refine BlockExponential.exp_span _ _ (fun φ hφ => BlockSlices.LS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩ r' hr' hrr c' hc'
  obtain ⟨ψ₁, -, h1, -, hexp⟩ := hT.left ψ hψ k g m₂
  have e : ℓ = ψ₁ := Subtype.ext (funext fun m₁ => (hℓ m₁).trans (h1 m₁).symm)
  rw [e] at hc'
  obtain ⟨φ, hφ, hcφ⟩ := hexp r' hr' hrr c' hc'
  have h := hNP φ hφ r' hr' (by omega) c' hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 =
      (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

theorem RS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ φ.1,
      c₂.re ≤ (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re := by
  refine BlockExponential.exp_span _ (fun r₂ => (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
    (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re) (fun φ hφ => BlockSlices.RS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩ r₂ hr₂ hrs c₂ hc₂
  obtain ⟨ψ₂, -, h1, -, hexp⟩ := hT.right ψ hψ k g m₁
  have e : ℓ = ψ₂ := Subtype.ext (funext fun m₂ => (hℓ m₂).trans (h1 m₂).symm)
  rw [e] at hc₂
  obtain ⟨φ, hφ, hcφ⟩ := hexp r₂ hr₂ hrs c₂ hc₂
  have h := hNP φ hφ (r + r₂) (by omega) (by omega) (c + c₂) hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  rw [Complex.add_re] at h
  have h2 : (c.re + c₂.re) / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 =
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

theorem LS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, -, h1, hc, -⟩ := hT.left ψ hψ k g m₂
    have e : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

theorem RS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, -, h1, hc, -⟩ := hT.right ψ hψ k g m₁
    have e : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end
