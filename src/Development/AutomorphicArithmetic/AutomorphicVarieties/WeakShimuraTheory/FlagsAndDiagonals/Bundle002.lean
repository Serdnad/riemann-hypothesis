module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Normal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ContConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.ResFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Lab.exNorm :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] (r : Γ →* M4 𝔞.V) (u : M4 𝔞.V) (pr : Bool) (g0 : Γ) (ν : 𝔞.V),
      𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _) → IsUnit (2 : 𝔞.V) → IsUnit ν → IsGSp ν (r g0) → IsGSp 1 u →
      ∀ X u' : M4 𝔞.V, X = adj (wM 𝔞.V pr) * r g0 * wM 𝔞.V pr → u' = adj (wM 𝔞.V pr) * u →
      (∀ i j, i ≠ j → X i j ∈ maximalIdeal 𝔞.V) → (∀ i j, i ≠ j → IsUnit (X i i - X j j)) →
      IsUnit (u' 0 0) → IsUnit (u' 0 0 * u' 1 1 - u' 0 1 * u' 1 0) →
      ∃ (P : PD Unit Γ 𝔞.V) (v b : M4 𝔞.V), 𝔞.Small P ∧ IsGSp 1 v ∧ Cg (maximalIdeal 𝔞.V) v 1 ∧
        (∀ g, P.r g = adj (wM 𝔞.V pr * v) * r g * (wM 𝔞.V pr * v)) ∧ (P.r g0).IsDiag ∧ IsLow (P.n ()) ∧ IsGSp 1 b ∧ IsUp b ∧
        adj (wM 𝔞.V pr * v) * u = P.n () * b := by
  intro l _ 𝔞 Γ _ _ r u pr g0 ν hs h2 hν hr hu X u' hX hu' hoff hdiag h00 hdet
  have gspAdj : ∀ {R : Type} [CommRing R] (μ : R) (g : M4 R), IsUnit μ → IsGSp μ g → IsGSp μ (adj g) := by
    intro R _ μ g hμ hg
    obtain ⟨c, rfl⟩ := hμ
    have hg' : adj g * g = (c : R) • (1 : M4 R) := hg
    have h1 : (((c⁻¹ : Rˣ) : R) • adj g) * g = 1 := by
      rw [Matrix.smul_mul, hg', smul_smul, Units.inv_mul, one_smul]
    have h2 : g * (((c⁻¹ : Rˣ) : R) • adj g) = 1 := mul_eq_one_comm.mp h1
    show adj (adj g) * adj g = (c : R) • (1 : M4 R)
    rw [adj_adj]
    calc g * adj g = (c : R) • (g * (((c⁻¹ : Rˣ) : R) • adj g)) := by
          rw [Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
      _ = (c : R) • (1 : M4 R) := by rw [h2]
  obtain ⟨S, _, _, _, f, P₁, hf, hc, hmap⟩ := hs
  haveI := hf.complete
  haveI := hf.loc
  have unitS : ∀ x : S, IsUnit (f x) ↔ IsUnit x := fun x => isUnit_map_iff f x
  have memS : ∀ x : S, x ∈ maximalIdeal S ↔ f x ∈ maximalIdeal 𝔞.V := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, unitS]
  have hr_eq : ∀ g, r g = (P₁.r g).map f := by
    intro g
    have := congrArg (fun P : PD Unit Γ 𝔞.V => P.r g) hmap
    exact this.symm
  have hu_eq : u = (P₁.n ()).map f := by
    have := congrArg (fun P : PD Unit Γ 𝔞.V => P.n ()) hmap
    exact this.symm
  have gspDown : ∀ (g : M4 S) (μ : S), IsGSp (f μ) (g.map f) → IsGSp μ g := by
    intro g μ h
    have h' : adj (g.map f) * g.map f = f μ • (1 : M4 𝔞.V) := h
    rw [adj_map, ← Matrix.map_mul] at h'
    show adj g * g = μ • (1 : M4 S)
    refine Matrix.ext fun i j => hf.inj ?_
    have := congrFun (congrFun h' i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set w₁ := wM S pr with hw₁
  set r₀ := P₁.r g0 with hr₀def
  set u₁ := P₁.n () with hu₁def
  have hwmap : wM 𝔞.V pr = w₁.map f := (wM_map f pr).symm
  have hXmap : X = (adj w₁ * r₀ * w₁).map f := by
    rw [hX, hr_eq, hwmap, adj_map, Matrix.map_mul, Matrix.map_mul]
  have hu'map : u' = (adj w₁ * u₁).map f := by
    rw [hu', hu_eq, hwmap, adj_map, Matrix.map_mul]
  set ν₁ := (adj r₀ * r₀) 0 0 with hν₁def
  have hE : (adj r₀ * r₀).map f = ν • (1 : M4 𝔞.V) := by
    rw [Matrix.map_mul, ← adj_map, ← hr_eq]
    exact hr
  have hν₁ : f ν₁ = ν := by
    have := congrFun (congrFun hE 0) 0
    simpa using this
  have hr₀ : IsGSp ν₁ r₀ := by
    apply gspDown
    rw [hν₁, ← hr_eq]
    exact hr
  have hu₁ : IsGSp 1 u₁ := by
    apply gspDown
    rw [map_one, ← hu_eq]
    exact hu
  have h2S : IsUnit (2 : S) := (unitS 2).mp (by rw [map_ofNat]; exact h2)
  have hνS : IsUnit ν₁ := (unitS ν₁).mp (hν₁ ▸ hν)
  have hadjw₁ : IsGSp 1 (adj w₁) := gspAdj 1 w₁ isUnit_one (wM_sp pr)
  have hX₁ : IsGSp ν₁ (adj w₁ * r₀ * w₁) := by
    have := gsp_mul (gsp_mul hadjw₁ hr₀) (wM_sp (R := S) pr)
    simpa using this
  have hoff₁ : ∀ i j, i ≠ j → (adj w₁ * r₀ * w₁) i j ∈ maximalIdeal S := by
    intro i j hij
    rw [memS]
    have := hoff i j hij
    rw [hXmap] at this
    exact this
  have hd₁ : ∀ i j, i ≠ j → IsUnit ((adj w₁ * r₀ * w₁) i i - (adj w₁ * r₀ * w₁) j j) := by
    intro i j hij
    rw [← unitS]
    have := hdiag i j hij
    rw [hXmap] at this
    simpa using this
  obtain ⟨v₁, hv₁, hv₁m, hv₁d, -⟩ := normal S ν₁ (adj w₁ * r₀ * w₁) h2S hX₁ hoff₁ hd₁ hνS
  have hcg : Cg (maximalIdeal S) v₁ 1 := by
    intro i j
    have := hv₁m i j
    rwa [Matrix.sub_apply] at this
  have hadjv : Cg (maximalIdeal S) (adj v₁) 1 := by
    have := Cg.adj hcg
    rwa [adj_one] at this
  have hcgu : Cg (maximalIdeal S) (adj v₁ * (adj w₁ * u₁)) (adj w₁ * u₁) := by
    have := Cg.mul hadjv (Cg.refl (adj w₁ * u₁))
    rwa [one_mul] at this
  have hq : ∀ i j, Ideal.Quotient.mk (maximalIdeal S) ((adj v₁ * (adj w₁ * u₁)) i j) = Ideal.Quotient.mk (maximalIdeal S) ((adj w₁ * u₁) i j) :=
    fun i j => Ideal.Quotient.eq.mpr (hcgu i j)
  have unitOf : ∀ a b : S, Ideal.Quotient.mk (maximalIdeal S) a = Ideal.Quotient.mk (maximalIdeal S) b → IsUnit b → IsUnit a := by
    intro a b hab hb
    by_contra ha
    have ha' : a ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal a).mpr ha
    have hb' : b ∈ maximalIdeal S := by
      have hd := Ideal.Quotient.eq.mp hab
      have := (maximalIdeal S).sub_mem ha' hd
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal b).mp hb' hb
  have h00₁ : IsUnit ((adj w₁ * u₁) 0 0) := by
    rw [← unitS]
    rw [hu'map] at h00
    exact h00
  have hdet₁ : IsUnit ((adj w₁ * u₁) 0 0 * (adj w₁ * u₁) 1 1 - (adj w₁ * u₁) 0 1 * (adj w₁ * u₁) 1 0) := by
    rw [← unitS]
    rw [hu'map] at hdet
    simpa using hdet
  have h00'' : IsUnit ((adj v₁ * (adj w₁ * u₁)) 0 0) := unitOf _ _ (hq 0 0) h00₁
  have hdet'' : IsUnit ((adj v₁ * (adj w₁ * u₁)) 0 0 * (adj v₁ * (adj w₁ * u₁)) 1 1 - (adj v₁ * (adj w₁ * u₁)) 0 1 * (adj v₁ * (adj w₁ * u₁)) 1 0) := by
    refine unitOf _ _ ?_ hdet₁
    simp only [map_sub, map_mul, hq]
  have hg'' : IsGSp 1 (adj v₁ * (adj w₁ * u₁)) := by
    have := gsp_mul (gspAdj 1 v₁ isUnit_one hv₁) (gsp_mul hadjw₁ hu₁)
    simpa using this
  obtain ⟨n₁, b₁, hn₁, hb₁, hbu₁, hnb⟩ := Lab.luSp S _ hg'' h00'' hdet''
  set p₁ := w₁ * v₁ with hp₁def
  have hp₁ : IsGSp 1 p₁ := by
    have := gsp_mul (wM_sp (R := S) pr) hv₁
    simpa using this
  have hleft : adj p₁ * p₁ = 1 := by
    have h : adj p₁ * p₁ = (1 : S) • (1 : M4 S) := hp₁
    rw [h, one_smul]
  have hright : p₁ * adj p₁ = 1 := by
    have h : adj (adj p₁) * adj p₁ = (1 : S) • (1 : M4 S) := gspAdj 1 p₁ isUnit_one hp₁
    rw [adj_adj, one_smul] at h
    exact h
  let r₂ : Γ →* M4 S :=
    { toFun := fun g => adj p₁ * P₁.r g * p₁
      map_one' := by
        simp only [map_one, mul_one]
        exact hleft
      map_mul' := by
        intro a b
        simp only [map_mul]
        calc adj p₁ * (P₁.r a * P₁.r b) * p₁ = adj p₁ * P₁.r a * (p₁ * adj p₁) * P₁.r b * p₁ := by
              rw [hright, mul_one]
              simp only [mul_assoc]
          _ = adj p₁ * P₁.r a * p₁ * (adj p₁ * P₁.r b * p₁) := by simp only [mul_assoc] }
  let P₂ : PD Unit Γ S := ⟨r₂, fun _ => n₁⟩
  have hcont : P₂.Cont (maximalIdeal S) := Lab.contConj Γ S (maximalIdeal S) (fun g => P₁.r g) (adj p₁) p₁ hc
  have hone : ∀ i j, (1 : M4 𝔞.V) i j = f ((1 : M4 S) i j) := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨P₂.map f, v₁.map f, b₁.map f, ⟨S, _, _, _, f, P₂, hf, hcont, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := gsp_map f hv₁
    rwa [map_one] at this
  · intro i j
    have := (memS _).mp (hcg i j)
    rw [map_sub, ← hone] at this
    exact this
  · intro g
    show (adj p₁ * P₁.r g * p₁).map f = _
    rw [hr_eq g, hwmap, ← Matrix.map_mul, adj_map, Matrix.map_mul, Matrix.map_mul]
  · show (adj p₁ * r₀ * p₁).map f |>.IsDiag
    have he : adj p₁ * r₀ * p₁ = adj v₁ * (adj w₁ * r₀ * w₁) * v₁ := by
      rw [hp₁def, adj_mul]
      simp only [mul_assoc]
    rw [he]
    exact hv₁d.map (map_zero f)
  · show IsLow (n₁.map f)
    obtain ⟨hn1, hn2, hn3⟩ := hn₁
    refine ⟨?_, ?_, ?_⟩
    · have := gsp_map f hn1
      rwa [map_one] at this
    · intro i
      simp [Matrix.map_apply, hn2 i]
    · intro i j hij
      simp [Matrix.map_apply, hn3 i j hij]
  · have := gsp_map f hb₁
    rwa [map_one] at this
  · intro i j hij
    simp [Matrix.map_apply, hbu₁ i j hij]
  · show adj (wM 𝔞.V pr * v₁.map f) * u = n₁.map f * b₁.map f
    rw [hu_eq, hwmap, ← Matrix.map_mul, adj_map, ← Matrix.map_mul, ← Matrix.map_mul, ← hnb]
    congr 1
    rw [adj_mul]
    simp only [mul_assoc]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem conj_flag {R : Type} [CommRing R] {m u n b : M4 R} (hm : IsGSp 1 m) (hb : IsGSp 1 b)
    (e : adj m * u = n * b) (X : M4 R) : adj n * (adj m * X * m) * n = b * (adj u * X * u) * adj b := by
  have hmm : ∀ Y : M4 R, m * (adj m * Y) = Y := fun Y => by
    rw [← mul_assoc, sp_mul_adj hm, one_mul]
  have hn : n = adj m * u * adj b := by
    rw [e, mul_assoc, sp_mul_adj hb, mul_one]
  rw [hn, adj_mul, adj_mul, adj_adj, adj_adj]
  simp only [mul_assoc, hmm]

private theorem low_mem {R : Type} [CommRing R] {I : Ideal R} {n : M4 R} (hn : IsLow n) (h10 : n 1 0 ∈ I) (h30 : n 3 0 ∈ I)
    (h21 : n 2 1 ∈ I) : ∀ i j, i ≠ j → wt i j ≠ -wPs → n i j ∈ I := by
  intro i j hij hw
  have hup : ∀ i j : Fin 4, i < j → n i j ∈ I := fun i j h => by
    rw [hn.2.2 i j h]
    exact I.zero_mem
  have hsp := congrFun (congrFun (sp_adj_mul hn.1) 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, hn.2.1, hn.2.2, UpperTheory.V.GradeZeroInterpolatingElement.sgn] at hsp
  have h32 : n 3 2 ∈ I := by
    have : n 3 2 = -n 1 0 := by linear_combination hsp
    rw [this]
    exact I.neg_mem h10
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact hup _ _ (by decide)
    | exact h10
    | exact h30
    | exact h21
    | exact h32
    | exact absurd (by simp [UpperTheory.V.GradeZeroInterpolatingElement.wt, UpperTheory.V.GradeZeroInterpolatingElement.wPs, UpperTheory.V.GradeZeroInterpolatingElement.lamW, UpperTheory.V.GradeZeroInterpolatingElement.muW]) hw

private theorem ps_chi {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
    (𝔞 : Amb l) {pr : Bool} (h : LabOk D pr) {s : G ℚ Ω} (hs : s ∈ D.Gp l) (i : Fin 4) :
    𝔞.a c (D.ps i s) - 𝔞.a c (chi D pr i s) ∈ maximalIdeal 𝔞.V := by
  have := 𝔞.loc c
  cases pr with
  | false =>
    have : chi D false i s = D.ps i s := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  | true =>
    have hbar : Raw.bar D.Psi s = 1 := h rfl s hs
    have hP : (↑(D.Psi s) : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one]
      have hb : residue c.O ↑(D.Psi s) = 1 := hbar
      rw [hb, sub_self]
    have hPm := map_nonunit (𝔞.a c) _ hP
    have key : ∀ x : (c.O)ˣ, 𝔞.a c ↑(x * D.Psi s) - 𝔞.a c ↑x ∈ maximalIdeal 𝔞.V := by
      intro x
      have e : 𝔞.a c (↑x * ↑(D.Psi s)) - 𝔞.a c ↑x = 𝔞.a c ↑x * 𝔞.a c (↑(D.Psi s) - 1) := by
        rw [map_mul, map_sub, map_one]
        ring
      rw [Units.val_mul, e]
      exact Ideal.mul_mem_left _ _ hPm
    have key' : ∀ x : (c.O)ˣ, 𝔞.a c ↑x - 𝔞.a c ↑(x * D.Psi s) ∈ maximalIdeal 𝔞.V := by
      intro x
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 (key x)
    fin_cases i
    · show 𝔞.a c ↑(D.th s) - 𝔞.a c ↑(D.al s) ∈ _
      have : D.th s = D.al s * D.Psi s := rfl
      rw [this]
      exact key _
    · show 𝔞.a c ↑(D.Psi s) - 𝔞.a c ↑((1 : G ℚ Ω →* (c.O)ˣ) s) ∈ _
      have : D.Psi s = (1 : G ℚ Ω →* (c.O)ˣ) s * D.Psi s := by simp
      rw [this]
      exact key _
    · show 𝔞.a c ↑(D.al s) - 𝔞.a c ↑(D.th s) ∈ _
      have : D.th s = D.al s * D.Psi s := rfl
      rw [this]
      exact key' _
    · show 𝔞.a c ↑((1 : G ℚ Ω →* (c.O)ˣ) s) - 𝔞.a c ↑(D.Psi s) ∈ _
      have : D.Psi s = (1 : G ℚ Ω →* (c.O)ˣ) s * D.Psi s := by simp
      rw [this]
      exact key' _

theorem UpperTheory.V.Ws.Lab.pairOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u →
      ∀ (pr : Bool) (g0 : G ℚ Ω) (P : PD Unit (G ℚ Ω) 𝔞.V) (v b : M4 𝔞.V), LabOk D pr → 𝔞.Small P → IsGSp 1 v → Cg (maximalIdeal 𝔞.V) v 1 →
      (∀ g, P.r g = adj (wM 𝔞.V pr * v) * r g * (wM 𝔞.V pr * v)) → (P.r g0).IsDiag → IsLow (P.n ()) → IsGSp 1 b → IsUp b →
      adj (wM 𝔞.V pr * v) * u = P.n () * b → QPair D pr g0 𝔞 P ∧ NearSplit D pr 𝔞 P := by
  intro Ω _ _ _ l _ c D hG 𝔞 r u hK pr g0 P v b hlab hsmall hv hvc hPr hdiag hlow hb hbup e
  have hMsp : IsGSp 1 (wM 𝔞.V pr * v) := sp_mul (wM_sp pr) hv
  have hwM : ∀ d : Fin 4 → 𝔞.V,
      adj (wM 𝔞.V pr) * Matrix.diagonal d * wM 𝔞.V pr = Matrix.diagonal (fun i => d (lab pr i)) := by
    intro d
    cases pr
    · simp [UpperTheory.V.Ws.wM, UpperTheory.V.Ws.lab, adj_one]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Ws.wM, UpperTheory.V.Ws.lab, Matrix.mul_apply,
        Fin.sum_univ_four, adj_apply, UpperTheory.V.GradeZeroInterpolatingElement.sgn, Matrix.diagonal, Fin.rev]
  have hflag : ∀ s ∈ D.Gp l, IsUp (adj (P.n ()) * P.r s * P.n ()) ∧
      ∀ i, (adj (P.n ()) * P.r s * P.n ()) i i = (adj u * r s * u) i i := by
    intro s hs
    rw [hPr s, conj_flag hMsp hb e (r s)]
    exact upConj 𝔞.V b _ hb hbup (hK.flag s hs)
  have hdr : ∀ (f : Fin 4 → G ℚ Ω →* (c.O)ˣ) (g : G ℚ Ω) (i j : Fin 4),
      𝔞.a c (diagRep f g i j) = Matrix.diagonal (fun i => 𝔞.a c ↑(f i g)) i j := by
    intro f g i j
    unfold UpperTheory.V.GradeZeroInterpolatingElement.diagRep
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hred : ∀ g i j, P.r g i j - 𝔞.a c (diagRep (chi D pr) g i j) ∈ maximalIdeal 𝔞.V := by
    intro g
    have hw : Cg (maximalIdeal 𝔞.V) (wM 𝔞.V pr) (wM 𝔞.V pr) := fun i j => by
      rw [sub_self]
      exact Ideal.zero_mem _
    have hM : Cg (maximalIdeal 𝔞.V) (wM 𝔞.V pr * v) (wM 𝔞.V pr * 1) := Cg.mul hw hvc
    rw [mul_one] at hM
    have hR : Cg (maximalIdeal 𝔞.V) (r g) (Matrix.diagonal fun i => 𝔞.a c ↑(D.ps i g)) := by
      intro i j
      have h1 := hK.red g i j
      have h2 : 𝔞.a c (D.r0 g i j) = Matrix.diagonal (fun i => 𝔞.a c ↑(D.ps i g)) i j := by
        unfold UpperTheory.V.GradeZeroInterpolatingElement.Raw.r0
        exact hdr D.ps g i j
      rwa [h2] at h1
    have hC := Cg.mul (Cg.mul (Cg.adj hM) hR) hM
    rw [hwM] at hC
    intro i j
    rw [hdr, hPr g]
    exact hC i j
  obtain ⟨hs, hsep⟩ := sg_sep hG 𝔞 pr
  have hX : Cg (maximalIdeal 𝔞.V) (P.r (D.sg l)) (Matrix.diagonal fun i => 𝔞.a c ↑(chi D pr i (D.sg l))) := by
    intro i j
    have := hred (D.sg l) i j
    rwa [hdr] at this
  obtain ⟨hfl, hdg⟩ := hflag (D.sg l) hs
  have hdiag' : ∀ i, (adj (P.n ()) * P.r (D.sg l) * P.n ()) i i - 𝔞.a c ↑(D.ps i (D.sg l)) ∈ maximalIdeal 𝔞.V := by
    intro i
    rw [hdg i]
    exact hK.char _ hs i
  obtain ⟨h10, h30, -, h4⟩ := resFlag 𝔞.V (P.r (D.sg l)) (P.n ()) (fun i => 𝔞.a c ↑(chi D pr i (D.sg l)))
    (fun i => 𝔞.a c ↑(D.ps i (D.sg l))) hX hlow.1 hfl hdiag' (fun i j h => hsep i j h)
  have h00 : P.n () 0 0 = 1 := hlow.2.1 0
  have h01 : P.n () 0 1 = 0 := hlow.2.2 0 1 (by decide)
  have h21 : P.n () 2 1 ∈ maximalIdeal 𝔞.V := by
    have := (h4 (by rw [h00]; exact isUnit_one)).2
    rwa [h00, h01, one_mul, zero_mul, sub_zero] at this
  refine ⟨⟨hsmall, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ⟨hred, low_mem hlow h10 h30 h21, ?_⟩⟩
  · intro g
    show IsGSp (𝔞.a c ↑(D.th g)) (P.r g)
    rw [hPr g]
    exact gsp_conj hMsp (hK.mult g)
  · intro g hg
    rcases hg with ⟨A, hA, hgA, hr⟩ | ⟨p, hp, hgp⟩
    · rw [hPr g, hK.unr A hA g hgA hr, mul_one, sp_adj_mul hMsp]
    · rw [hPr g, hK.atP p hp g hgp, mul_one, sp_adj_mul hMsp]
  · exact hdiag
  · intro w
    exact hlow
  · intro w s hs'
    exact (hflag s hs').1
  · intro w s hs'
    exact absurd hs' (Set.notMem_empty s)
  · intro s hs' i
    have hs'' : s ∈ D.Gp l := Ine_le_Dec (F := ℚ) (D.pl l) hs'
    show (adj (P.n ()) * P.r s * P.n ()) i i = _
    rw [(hflag s hs'').2 i]
    exact hK.inert s hs' i
  · intro s hs' i
    show (adj (P.n ()) * P.r s * P.n ()) i i - _ ∈ _
    rw [(hflag s hs').2 i]
    have h1 := hK.char s hs' i
    have h2 := ps_chi 𝔞 hlab hs' i
    have h3 := Ideal.add_mem _ h1 h2
    convert h3 using 1
    ring
end
