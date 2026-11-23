module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct



namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

theorem splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

theorem splitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hv, by rw [cA_cA, add_comm, h3]⟩

theorem idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact ⟨Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1,
    Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (splitIdem_cA (hes PP hPP).1)⟩

theorem idemSum_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) :
    finPart D e ∈ intAE D ∧ finPart D (cA D e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine ⟨?_, ?_⟩

  · rw [map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (hes PP hPP).1

  · rw [map_sum, map_sum]
    exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (splitIdem_cA (hes PP hPP).1)

theorem infPart_fI : infPart D (fI D) = 0 := by
  show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 0
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem half_infPart {m n : ℕ} {f : AE D} (hf : f * fI D = f) {y : Mx D m n} (hy : IsHalf f y) :
    y.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  calc infPart D (y i j) = infPart D ((f * fI D) * y i j) := by rw [hf, hy i j]
    _ = 0 := by rw [map_mul, map_mul, infPart_fI, mul_zero, zero_mul]

variable (S T : HSp D)

theorem hO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    hO S T y u = hO S T y (f • u) := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  conv_lhs => rw [← hy d a]
  ring

theorem symplO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    symplO S T y u = symplO S T y (f • u) := by
  unfold symplO; rw [hO_half_right S T hy u]

variable {S T}

theorem placeLatDualIi_of (hL : LatSelfDual D) : PlaceLatDualIi D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he y hy
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, hfc⟩ := idemSum_mul_fI he
  have hie := (idemSum_int he).1
  have hee := idemSum_mul_self he
  have hy0 : y.map (infPart D) = 0 := half_infPart hfc hy
  constructor
  · intro hx
    refine (hL4 y hy0).2 fun u hu => ?_
    have hm : e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hie hu
    have hh : IsHalf e (e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
    have h1 := hx _ hm hh
    rw [symplO_half_right S T hy u, symplO_swap S T (e • u) y, AddChar.map_neg_eq_inv, h1, inv_one]
  · intro hyL x hx hxh
    exact (hL4 x (half_infPart hfe hxh)).1 hx y hyL

theorem placeLatDualIii_of (hL : LatSelfDual D) : PlaceLatDualIii D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he x hx
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, -⟩ := idemSum_mul_fI he
  have hic := (idemSum_int he).2
  have hee := idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hx0 : x.map (infPart D) = 0 := half_infPart hfe hx
  have hxc : IsHalf (cA D (cA D e)) x := by rw [cA_cA]; exact hx
  constructor
  · intro hy
    refine (hL4 x hx0).2 fun u hu => ?_
    have hm : cA D e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hic hu
    have hh : IsHalf (cA D e) (cA D e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
    rw [symplO_half_right S T hxc u]
    exact hy _ hm hh
  · intro hxL y hy _
    exact (hL4 x hx0).1 hxL y hy

end Formalism.IndefR.Fin.PDA

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct Pointwise



namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem xi_AA_AAbar : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA *
    D.host.AAbar = FractionalIdeal.dual ℤ ℚ 1 := by
  have hfp := factPrincipalDatum D.R D.host
  have hdd := coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)
  have := eq_inv_of_mul_eq_one_left hfp
  rw [this]
  show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _
  rw [hdd, inv_inv]

theorem one_ne_zero' : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot

theorem dual_ne_zero' : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero'

theorem AA_ne_zero : D.host.AA ≠ 0 := by
  intro h0
  have h := xi_AA_AAbar (D := D)
  rw [h0, mul_zero, zero_mul] at h
  exact dual_ne_zero' h.symm



theorem mem_AA_of_trace {z : D.host.E}
    (h : ∀ c ∈ D.host.AA, Algebra.trace D.host.F D.host.E (D.host.xi0 * (star c * z)) ∈ invDiff D.host.F) :
    z ∈ D.host.AA := by
  have hX := xi_AA_AAbar (D := D)
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero'
  have hmem : ∀ j ∈ D.host.AAbar, D.host.xi0 * z * j ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro j hj
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    have hc : D.host.conj j ∈ D.host.AA := Formalism.L2.Pj.conj_mem_AA D hj
    have hco : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) ∈ D.host.AA := by
      have e : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) = starO o • D.host.conj j := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [e]; exact Submodule.smul_mem _ _ hc
    obtain ⟨k, hk⟩ := h _ hco 1
    rw [show ((1 : 𝓞 D.host.F) : D.host.F) = 1 from rfl, mul_one] at hk
    have hs : star (D.host.conj j) = j := by
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.MainNotions.UnusedSlot33.HK.conj_conj]
    have he : D.host.xi0 * (star (D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o)) * z) =
        D.host.xi0 * z * j * algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [star_mul', star_star, hs]; ring
    rw [he] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := D.host.F), hk, eq_intCast]
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 * z) * D.host.AAbar ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r (hmem j hj)
  set Y := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AAbar with hYdef
  have hAY : D.host.AA * Y = FractionalIdeal.dual ℤ ℚ 1 := by rw [← hX, hYdef]; ring
  have hY : Y ≠ 0 := by
    have h0 : D.host.AA * Y ≠ 0 := by rw [hAY]; exact dual_ne_zero'
    exact right_ne_zero_of_mul h0
  have hzY : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y ≤ D.host.AA * Y := by
    rw [hAY, hYdef, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm z]
    exact hle
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA :=
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y * Y⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
      _ ≤ D.host.AA * Y * Y⁻¹ := by gcongr
      _ = D.host.AA := by rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
  exact hsp (FractionalIdeal.mem_spanSingleton_self _ _)

theorem hF_smul_right (T : HSp D) (x v : Fin T.rank → D.host.E) (j : D.host.E) :
    hF T x (j • v) = j * hF T x v := by
  unfold hF
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ind_of_hF {T : HSp D} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    {v : Fin T.rank → D.host.E} (hv : ∀ t ∈ ΛT, hF T t v ∈ D.host.AA) (P : (Fin T.rank → D.host.E) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hgen : ∀ a ∈ D.host.AA, ∀ t ∈ ΛT, P (a • t)) : P v := by
  have hA := AA_ne_zero (D := D)
  have key : ∀ x ∈ D.host.AA * D.host.AA⁻¹, P (x • v) := by
    intro x hx
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro i hi j hj
      have hjv : j • v ∈ ΛT := by
        refine (hT.2 (j • v)).2 fun t ht => ?_
        have hm : j * hF T t v ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hj (hv t ht)
        rw [inv_mul_cancel₀ hA] at hm
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hm
        refine ⟨b, ?_⟩
        rw [show (b : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b from rfl, hb, ← hF_smul_right]
        rfl
      rw [mul_smul]
      exact hgen i hi _ hjv
    · intro x y hx hy
      rw [add_smul]
      exact hadd _ _ hx hy
  have h1 : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
    rw [mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  simpa using key 1 h1

abbrev rkSpan (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Submodule ℤ (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t}

theorem hF_mulVec (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ∑ cc, ∑ d, star (t cc) * T.gram cc d * ∑ a, γ d a * s a = hF T t (γ.mulVec s) := by
  unfold hF
  simp only [Matrix.mulVec, dotProduct]

theorem globalDual_of_basis (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    (hB : ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (h : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) :
    γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t} := by
  obtain ⟨N, g, s', hg, hs', hid⟩ := hB
  have h1 : ∀ s ∈ ΛS, ∀ t ∈ ΛT, hF T t (γ.mulVec s) ∈ D.host.AA := by
    intro s hs t ht
    apply mem_AA_of_trace
    intro c hc
    have := h c hc s hs t ht
    unfold betaO at this
    rwa [hermitian_rank_one_right, hF_mulVec] at this
  have h2 : ∀ s ∈ ΛS, ∀ v : Fin T.rank → D.host.E, (∀ t ∈ ΛT, hF T t v ∈ D.host.AA) →
      rk1 S T 1 s v ∈ rkSpan S T ΛS ΛT := by
    intro s hs v hv
    refine ind_of_hF hT hv (fun w => rk1 S T 1 s w ∈ rkSpan S T ΛS ΛT) ?_ ?_ ?_
    · have : rk1 S T 1 s 0 = 0 := by ext i j; simp [rk1]
      simp only [this]; exact zero_mem _
    · intro x y hx hy
      have : rk1 S T 1 s (x + y) = rk1 S T 1 s x + rk1 S T 1 s y := by
        ext i j; simp only [rk1, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; ring
      simp only [this]; exact add_mem hx hy
    · intro a ha t ht
      have : rk1 S T 1 s (a • t) = rk1 S T a s t := by
        ext i j; simp only [rk1, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]; ring
      simp only [this]
      exact Submodule.subset_span ⟨a, ha, s, hs, t, ht, rfl⟩
  have h3 : γ = ∑ i, rk1 S T 1 (s' i) (γ.mulVec (g i)) := by
    refine Matrix.ext fun a j => ?_
    have hj : γ.mulVec (∑ i, hF S (s' i) (Pi.single j 1) • g i) a = γ.mulVec (Pi.single j 1) a :=
      congrArg (fun w => γ.mulVec w a) (hid (Pi.single j 1))
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hj
    rw [← hj]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.sum_apply, rk1, Matrix.of_apply, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : hF S (s' i) (Pi.single j 1) = ∑ k, star (s' i k) * S.gram k j := by
      unfold hF
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Pi.single_apply]
    rw [e]; ring
  rw [h3]
  exact Submodule.sum_mem _ fun i _ => h2 (s' i) (hs' i) _ fun t ht => h1 (g i) (hg i) t ht

end Formalism.IndefR.Fin.PDA

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct



namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}



theorem lat_ann (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ψ (symplO S T x u) = 1 := by
  have inner : ∀ {α : Af D.host.F} {c : D.host.E} {s : Fin S.rank → D.host.E} {t : Fin T.rank → D.host.E},
      α ∈ intAf D.host.F → c ∈ D.host.AA → s ∈ ΛS → t ∈ ΛT →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 α • ratW T S (rk1 S T c s t)) u) = 1 := by
    intro α c s t hα hc hs ht u hu
    induction hu using AddSubgroup.closure_induction with
    | mem u' hu' =>
      obtain ⟨α', hα', -, c', hc', s', hs', t', ht', rfl⟩ := hu'
      rw [gen_eq]
      exact psi_gen hψ S T hS hT hα hα' hc hc' hs hs' ht ht'
    | zero => rw [symplO_zero_right, AddChar.map_zero_eq_one]
    | add u1 u2 _ _ h1 h2 => rw [symplO_add_right, AddChar.map_add_eq_mul, h1, h2, one_mul]
    | neg u' _ h => rw [symplO_neg_right, AddChar.map_neg_eq_inv, h, inv_one]
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx'
    rw [gen_eq]
    exact inner hα hc hs ht u hu
  | zero => rw [symplO_zero_left, AddChar.map_zero_eq_one]
  | add x1 x2 _ _ h1 h2 => rw [symplO_add_left, AddChar.map_add_eq_mul, h1, h2, one_mul]
  | neg x' _ h => rw [symplO_neg_left, AddChar.map_neg_eq_inv, h, inv_one]

end Formalism.IndefR.Fin

end
end
