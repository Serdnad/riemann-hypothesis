module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle711
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle718
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle712
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle717
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem linearOn_of_forall_inRCone {O : Type} [CommRing O] (χ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin n → LinearMap.BilinForm ℤ X}
    (hχ : χ.LinearOn γ) (h : ∀ j, InRCone γ (γ' j)) : χ.LinearOn γ' := by
  intro c hc
  choose a ha he using h
  have hpt : ∀ j x y, (γ' j x y : ℝ) = ∑ i, a j i * (γ i x y : ℝ) := by
    intro j x y
    have := LinearMap.congr_fun₂ (he j) x y
    simpa [LinearMap.sum_apply] using this
  have hev : ∀ j, χ.evalZ (γ' j) = ∑ i, a j i * χ.evalZ (γ i) := by
    intro j
    rw [← hχ (a j) (ha j)]
    simp only [InvFun.evalZ, hpt]
  have e : (fun x y => ∑ j, c j * (γ' j x y : ℝ)) = fun x y => ∑ i, (∑ j, c j * a j i) * (γ i x y : ℝ) := by
    funext x y
    simp only [hpt, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e, hχ _ (fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j i))]
  simp only [hev, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem subordinate_of_isStarOf : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O),
    IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  intro O _ bar q ψ w ψ' hs χ hχ X _ _ _ _ hX n γ' hγ'
  rcases hs.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, -, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, -, -, -, hβ₀, -, -, hin⟩
  · exact linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) hin
  · refine linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) fun j => inRCone_trans (fun k => ?_) (hin j)
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hβ₀
    · simpa using inRCone_self γ (s k)

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isCell_face_of_isFaceCut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ)
    (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  intro E _ _ _ H q ψ hψ X _ _ _ _ hX hD m v hv m' s h hcut
  have hP := hψ X hX
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNr e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hℓpos
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ γ ∈ S, ψ.evalZ γ ≤ b := by
    refine ⟨⌈∑ γ ∈ hS.toFinset, |ψ.evalZ γ|⌉₊, fun γ hγ => ?_⟩
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun γ => |ψ.evalZ γ|) (fun _ _ => abs_nonneg _) (hS.mem_toFinset.2 hγ))
  set K : ℕ := C * (1 + N * b) + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _

  have gen : ∀ u ∈ balForms H.bar X, (∀ y, 0 ≤ u y y) → ψ.evalZ u ≤ b →
      (0 ≤ h u ∧ (ℓ u : ℝ) = N * ψ.evalZ u) ∨
        (0 : ℝ) < K * (ℓ u : ℝ) + h u - K * N * ψ.evalZ u := by
    intro u hu hp hub
    by_cases heq : (ℓ u : ℝ) = N * ψ.evalZ u
    · left
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp heq.symm
      have e1 : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (v i) := by
        have := congrArg h hc

        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
      have hnn : 0 ≤ (k : ℤ) * h u := e1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hcut.1 i)
      exact ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hk)).1 hnn, heq⟩
    · right
      obtain ⟨n, hn⟩ := hP.integral u hu hp
      have hle : (N : ℝ) * ψ.evalZ u ≤ ℓ u := h2 u hu hp
      have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne hle (Ne.symm heq)
      rw [hn] at hlt hub ⊢
      have hint : (N : ℤ) * n + 1 ≤ ℓ u := by
        have : (((N : ℤ) * n : ℤ) : ℝ) < ℓ u := by push_cast; exact hlt
        exact_mod_cast this
      have hint' : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast hint
      have hCu : -h u ≤ C * ℓ u := by simpa using hC u hu hp
      have hCu' : -(h u : ℝ) ≤ C * ℓ u := by exact_mod_cast hCu
      have hKr : (K : ℝ) = C * (1 + N * b) + 1 := by rw [hK]; push_cast; ring
      have hCN : (0 : ℝ) ≤ C * N := by positivity
      have a1 : (K - C : ℝ) * 1 ≤ (K - C) * (ℓ u - N * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [hKr]; have : (0 : ℝ) ≤ C * N * b := by positivity
                                                    nlinarith)
      have a2 : (C * N : ℝ) * n ≤ C * N * b := mul_le_mul_of_nonneg_left hub hCN
      rw [hKr] at a1 ⊢
      nlinarith

  have core : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ((K * N : ℕ) : ℝ) * ψ.evalZ β ≤ ((K • ℓ + h) β : ℤ) ∧
        (((K * N : ℕ) : ℝ) * ψ.evalZ β = ((K • ℓ + h) β : ℤ) → h β = 0) := by
    intro β hβ hp
    have hR : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ])
        (by simp [hp]) (by simp)
    obtain ⟨e, mm, γ, c, hγ, hγS, hc, hsum⟩ := hcov (toReal β) hR
    set u : Fin mm → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hu
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply, u] using this
    have hlin : ψ.LinearOn u := (linearOn_pull_iff e.symm.surjective).2 hγ.linear
    have hψβ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu, (linearOn_iff ψ u).1 hlin c hc]
    have hℓβ := apply_eq_of_toReal_eq hβu ℓ
    have hhβ := apply_eq_of_toReal_eq hβu h
    have hT : (((K • ℓ + h) β : ℤ) : ℝ) - ((K * N : ℕ) : ℝ) * ψ.evalZ β =
        ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul]
      rw [hℓβ, hhβ, hψβ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hg : ∀ i, (0 ≤ h (u i) ∧ (ℓ (u i) : ℝ) = N * ψ.evalZ (u i)) ∨
        (0 : ℝ) < K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i) := fun i =>
      gen (u i) (pull_mem _ (hγ.mem i)) (fun y => hγ.nonneg i _)
        (by rw [hu, evalZ_pull ψ e.symm.surjective]; exact hb _ (hγS i))
    have hterm : ∀ i, 0 ≤ c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := fun i => by
      refine mul_nonneg (hc i) ?_
      rcases hg i with ⟨h0, he⟩ | hpos
      · rw [he]
        have : (0 : ℝ) ≤ h (u i) := by exact_mod_cast h0
        nlinarith
      · exact hpos.le
    refine ⟨?_, fun heq => ?_⟩
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    · have h0 : ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) = 0 := by
        rw [← hT, heq, sub_self]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 h0
      have : (h β : ℝ) = 0 := by
        rw [hhβ]
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases eq_or_ne (c i) 0 with hci | hci
        · rw [hci, zero_mul]
        · have hTi := (mul_eq_zero.1 (hz i hi)).resolve_left hci
          rcases hg i with ⟨-, he⟩ | hpos
          · rw [he] at hTi
            have : (h (u i) : ℝ) = 0 := by linarith
            rw [this, mul_zero]
          · exact absurd hTi hpos.ne'
      exact_mod_cast this
  refine ⟨fun j => hv.mem _, fun j => hv.nonneg _, linearOn_comp hv.linear s, K * N, K • ℓ + h,
    Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => (core β hβ hp).1, fun β hβ hp heq => ?_⟩
  · have hz : h (v (s i)) = 0 := (hcut.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hz, add_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    rw [h1]; ring
  · have hh := (core β hβ hp).2 heq
    have hℓ : (N : ℝ) * ψ.evalZ β = ℓ β := by
      have e1 := heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hh, add_zero, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul] at e1
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have : (K : ℝ) * (N * ψ.evalZ β - ℓ β) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_left hKr.ne']
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp hℓ
    have e1 : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (v j) := by
      have := congrArg h hc

      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    rw [hh, mul_zero] at e1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (Int.natCast_nonneg (c j)) (hcut.1 j)).1 e1.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
      have hne : h (v j) ≠ 0 := fun h0 => hj ((hcut.2 j).1 h0)
      have := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
      exact_mod_cast this
    refine ⟨k, fun i => c (s i), hk, ?_⟩
    rw [hc]
    classical
    rw [← Finset.sum_map Finset.univ s (fun j => c j • v j)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

end GlobalTheory.PolFan
end
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LieBase.GramSmooth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts p σ}

theorem cInfAt_mul {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sub {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z - g z) y :=
  hf.comp₂ hg (G := fun x => x.1 - x.2) (contDiff_fst.sub contDiff_snd)

def CxInf (f : GlobalTheory.CxPts p σ → ℂ) (y : GlobalTheory.CxPts p σ) : Prop :=
  CInfAt (fun z => (f z).re) y ∧ CInfAt (fun z => (f z).im) y

variable {f g : GlobalTheory.CxPts p σ → ℂ}

theorem CxInf.mul (hf : CxInf f y) (hg : CxInf g y) : CxInf (fun z => f z * g z) y := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re]; exact cInfAt_sub (cInfAt_mul hf.1 hg.1) (cInfAt_mul hf.2 hg.2)
  · simp only [Complex.mul_im]; exact (cInfAt_mul hf.1 hg.2).add (cInfAt_mul hf.2 hg.1)

theorem CxInf.star (hf : CxInf f y) : CxInf (fun z => star (f z)) y := by
  refine ⟨?_, ?_⟩
  · simpa [Complex.star_def] using hf.1
  · simpa [Complex.star_def] using hf.2.neg

theorem CxInf.sum {κ : Type} (s : Finset κ) {f : κ → GlobalTheory.CxPts p σ → ℂ} (h : ∀ a ∈ s, CxInf (f a) y) :
    CxInf (fun z => ∑ a ∈ s, f a z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_⟩ <;> simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_insert ha, Complex.add_re]; exact h1.1.add h2.1
    · simp only [Finset.sum_insert ha, Complex.add_im]; exact h1.2.add h2.2

theorem cxInf_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : GlobalTheory.CxPts X.str σ} {f : X.Fn}
    (hf : RegAt (under y) f) : CxInf (fun z => ratVal f z) y :=
  ⟨GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
               (G := fun v => (v ()).re) (Complex.reCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) ())),
    GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
      (G := fun v => (v ()).im) (Complex.imCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) ()))⟩

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem cInfAt_comp {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'}
    {σ : k →+* ℂ} {σ' : k' →+* ℂ} {π : Y' ⟶ Y} {m : GlobalTheory.CxPts p' σ' → GlobalTheory.CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ π)
    {f : GlobalTheory.CxPts p σ → ℝ} {z : GlobalTheory.CxPts p' σ'} (h : CInfAt f (m z)) : CInfAt (fun w => f (m w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, (mem_ptsIn_preimage hm).2 h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_of_comp hm] using h₃
  · simp only [← ev_of_comp hm]
    exact (continuous_of_comp hm).continuousAt.eventually h₅

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem eventually_mem : ∀ (F : Type) [Field F] (X : Var F) (σ : F →+* ℂ) (ι : Type) [Finite ι] (m : ι → ℕ) (S : Fr (ratOf X) m 0) (y : GlobalTheory.CxPts X.str σ) (A : Mat m X.Fn), A ∈ S.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  intro F _ X σ ι _ m S y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem gram_entry_cInfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ (τ : E →+* ℂ) (p q : Fin (Dw.mult τ)) (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) → cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 → ∃ h : GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → ℂ, CInfAt (fun z => (h z).re) y ∧ CInfAt (fun z => (h z).im) y ∧ ∀ᶠ z in 𝓝 y, ∀ (hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z)), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → G.gram (cxOf e σ hj z) f τ p q = h z := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j hj V φ Φ hφ τ p q y hy hyV
  obtain ⟨g, hre, him, hg⟩ := hG V φ Φ τ p q hφ
  have hT : IsOpen ({y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1) := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hm : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), (cxOf e σ hj z).1 = z.1 ≫ j := fun _ => rfl
  have hyT : cxOf e σ hj y ∈ {y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1 :=
    ⟨mem_ptsIn.1 ((mem_ptsIn_preimage hm).1 hy), hyV⟩
  have cre := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 hre _ hyT
  have cim := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 him _ hyT
  refine ⟨fun z => g (cxOf e σ hj z), GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cre,
    GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cim, ?_⟩
  filter_upwards [(continuous_of_comp hm).continuousAt.preimage_mem_nhds (hT.mem_nhds hyT)] with z hz hz' f hf
  exact hg _ hz.1 hz' f hf

end GlobalTheory.LieBase.GramSmooth

theorem GlobalTheory.LieBase.cInfAt_gramOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j f₀ S A₀ hj hoi hT y hy A hA τ a b
  obtain ⟨U, hU, φ, Φ, hzU, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 := mem_ptsIn.2 hzU
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β Z σ F e X j f₀ S A₀ hj hoi hT V φ Φ hφ' A
  choose h hre him hev using fun p q => GlobalTheory.LieBase.GramSmooth.gram_entry_cInfAt E H Dw l Xo c O β Z σ G hG F e X j hj V φ Φ hφ' τ p q y hy hyV
  have hS := GlobalTheory.LieBase.GramSmooth.eventually_mem F X (σ.comp e.toRingHom) (E →+* ℂ) Dw.mult S y A hA
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have hall := Filter.eventually_all.2 fun pq : Fin (Dw.mult τ) × Fin (Dw.mult τ) => hev pq.1 pq.2
  have hreg := (hM y hA hyV).1 τ
  have key : ∀ᶠ z in 𝓝 y, gramOf e G hj f₀ A₀ A z τ a b =
      ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z := by
    filter_upwards [hS, hVn, hall] with z hzS hzV hzall
    obtain ⟨-, hex, hco⟩ := hM z hzS hzV
    have hov : σ = (evHom hzV).comp φ := GlobalTheory.ShFam.EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [gramOf, dite_eq_left hex]
    show (G.gram (cxOf e σ hj z) hex.choose τ)ᵀ a b = _
    rw [Matrix.transpose_apply, G.change (cxOf e σ hj z) f, hco _ hex.choose_spec f hf τ]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hzall (p, q) hzV f hf]
  open GlobalTheory.LieBase.GramSmooth in
  have hC : CxInf (fun z => ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z) y :=
    CxInf.sum _ fun q _ => (CxInf.sum _ fun p _ => (cxInf_ratVal (hreg p b)).star.mul ⟨hre p q, him p q⟩).mul
      (cxInf_ratVal (hreg q a))
  exact ⟨hC.1.congr (key.mono fun z hz => congrArg Complex.re hz), hC.2.congr (key.mono fun z hz => congrArg Complex.im hz)⟩

end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.superadditive_of_cells_cover_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X), evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  first | exact @GlobalTheory.PolFan.CoverSuper.superadd_of_cover | exact GlobalTheory.PolFan.CoverSuper.superadd_of_cover | (intros; apply GlobalTheory.PolFan.CoverSuper.superadd_of_cover <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.mem_span_of_chernClassesOfRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ), chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪ {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  first | exact @GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | exact GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | (intros; apply GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.homogeneousComponent_chernClassesOfRoots : ∀ {ι : Type} (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), homogeneousComponent d (chernRoots m Q) = chernRoots m (weightedHomogeneousComponent Prod.snd d Q) := by
  first | exact @GlobalTheory.GrassComp.homogeneousComponent_chernRoots | exact GlobalTheory.GrassComp.homogeneousComponent_chernRoots | (intros; apply GlobalTheory.GrassComp.homogeneousComponent_chernRoots <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem _root_.GlobalTheory.T.exists_member_of_construction_steps_secondPass : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  first | exact @GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | exact GlobalTheory.Mem.Top.Bl.memberE_of_steps2 | (intros; apply GlobalTheory.Mem.Top.Bl.memberE_of_steps2 <;> assumption)

end GlobalTheory.Mem.Top.Bl
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

theorem _root_.GlobalTheory.T.orthonormalFrames_lie_coordinates_unitary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x x₁ : (U.X k).dom), IsOrth (U.X k) x.1 → IsOrth (U.X k) x₁.1 → (U.un k x₁).x = (U.un k x).x → ∀ (τ : E →+* ℂ) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ b, Formalism.L2.Pj.IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => (T b' b : ℂ)) ((U.un k x₁).u τ b)) → Tᴴ * T = 1 := by
  first | exact @GlobalTheory.ShFam.lie_coord_unitary | exact GlobalTheory.ShFam.lie_coord_unitary | (intros; apply GlobalTheory.ShFam.lie_coord_unitary <;> assumption)
end
