module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open TensorProduct

private theorem ladder {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (h : ∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) (u : ℂ ⊗[ℤ] (X →₀ ℤ)) :
    f' (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X u) = TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y (f.lTensor ℂ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul c v =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | single x n =>
      have e1 : TensorProduct.finsuppScalarRight ℤ ℤ ℂ X (c ⊗ₜ[ℤ] Finsupp.single x n)
          = ((n : ℂ) * c) • Finsupp.single x (1 : ℂ) := by
        ext x'
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
        by_cases hx : x = x'
        · subst hx; simp
        · simp [Finsupp.single_apply, hx]
      have e2 : Finsupp.single x n = n • Finsupp.single x (1 : ℤ) := by simp
      ext y
      rw [e1, map_smul, LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, e2, map_smul,
        Finsupp.smul_apply, Finsupp.smul_apply, h]
      simp only [smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      push_cast
      ring

theorem UpperTheory.exactBase_integral_to_complex :
    UpperTheory.V.Af.BA.ExactBase := by
  intro X Y Z f g f' g' hf hg hfg
  classical
  have hex := Module.Flat.lTensor_exact ℂ hfg
  refine Function.Exact.of_ladder_addEquiv_of_exact
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ X).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Y).toAddEquiv
    (TensorProduct.finsuppScalarRight ℤ ℤ ℂ Z).toAddEquiv
    (f₁₂ := (f.lTensor ℂ).toAddMonoidHom) (f₂₃ := (g.lTensor ℂ).toAddMonoidHom)
    (g₁₂ := f'.toAddMonoidHom) (g₂₃ := g'.toAddMonoidHom) ?_ ?_ hex
  · exact AddMonoidHom.ext fun u => ladder f f' hf u
  · exact AddMonoidHom.ext fun u => ladder g g' hg u
end

section

open CategoryTheory

theorem UpperTheory.altChain_of_permSplit :
    UpperTheory.V.Af.BA.PermSplit → UpperTheory.V.Af.BA.AltChain := by
  intro hP Γ I _ _ K p
  simp only [UpperTheory.V.Af.BA.Cx.alt, UpperTheory.V.Af.BA.Cx.d, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, UpperTheory.V.Af.BA.Cx.reC_comp]
  simp only [Finset.smul_sum, smul_smul]
  set c : ℂ := ((p + 1 + 1).factorial : ℂ)⁻¹ with hc
  have hx : ∀ x : Fin (p + 2),
      ∑ σ : Equiv.Perm (Fin (p + 2)),
        ((-1 : ℂ) ^ (x : ℕ) * (c * (((Equiv.Perm.sign σ : ℤ)) : ℂ))) • K.reC (σ ∘ x.succAbove) =
      ∑ q : Fin (p + 2) × Equiv.Perm (Fin (p + 1)),
        (c * ((-1 : ℂ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℤ) : ℂ))) • K.reC (q.1.succAbove ∘ q.2) := by
    intro x
    obtain ⟨e, he⟩ := hP (p + 1) x
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, τ⟩ -
    obtain ⟨hs, hk⟩ := he i τ
    have hf : (e (i, τ) : Fin (p + 2) → Fin (p + 2)) ∘ x.succAbove = i.succAbove ∘ τ := funext hk
    rw [hf, hs]
    congr 1
    push_cast
    have h1 : (-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (c * (-1 : ℂ) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * h1
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  conv_rhs => rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, τ⟩ -
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hF : ((p + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hP2 : ((p : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : p + 2 ≠ 0)
  rw [hc, Nat.factorial_succ (p + 1)]
  push_cast
  field_simp
  ring_nf
  have h2 : (2 + (p : ℂ)) ≠ 0 := by rwa [add_comm]
  field_simp
  ring
end

section

private theorem fixOrb_reps {Z T : Type} (f : Z → T) (W : Set Z) (h : (f '' W).Finite) :
    ∃ B : Set Z, B ⊆ W ∧ B.Finite ∧ ∀ z ∈ W, ∃ z' ∈ B, f z' = f z := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · exact ⟨∅, by simp, Set.finite_empty, by simp [hW]⟩
  · haveI : Nonempty Z := ⟨w⟩
    refine ⟨Function.invFunOn f W '' (f '' W), ?_, h.image _, ?_⟩
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Function.invFunOn_mem ⟨z, hz, rfl⟩
    · intro z hz
      exact ⟨Function.invFunOn f W (f z), ⟨f z, ⟨z, hz, rfl⟩, rfl⟩,
        Function.invFunOn_eq ⟨z, hz, rfl⟩⟩

theorem UpperTheory.fixedOrbits_finite_representatives :
    UpperTheory.V.Af.BA.FixOrb := by
  classical
  intro G Z _ _ σ s hs W hfix hstab ⟨R, hR, hRW⟩
  have himg : ((fun z => MulAction.orbit G z) '' W).Finite := by
    refine (hR.image (fun z => MulAction.orbit G z)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := hRW z hz
    exact ⟨g • z, hg, MulAction.orbit_smul g z⟩
  obtain ⟨B1, hB1W, hB1, hB1r⟩ := fixOrb_reps _ W himg
  have hb : ∀ z ∈ W, ∃ b ∈ B1, ∃ h : G, h • b = z := by
    intro z hz
    obtain ⟨b, hbB, hbo⟩ := hB1r z hz
    have hbo' : MulAction.orbit G b = MulAction.orbit G z := hbo
    have hm : z ∈ MulAction.orbit G b := by
      rw [hbo']
      exact MulAction.mem_orbit_self z
    obtain ⟨h, hh⟩ := hm
    exact ⟨b, hbB, h, hh⟩
  let bb : Z → Z := fun z => if hz : z ∈ W then (hb z hz).choose else z
  let hh : Z → G := fun z => if hz : z ∈ W then (hb z hz).choose_spec.2.choose else 1
  have bbB : ∀ z ∈ W, bb z ∈ B1 := fun z hz => by
    simp only [bb, dif_pos hz]
    exact (hb z hz).choose_spec.1
  have hhb : ∀ z ∈ W, hh z • bb z = z := fun z hz => by
    simp only [bb, hh, dif_pos hz]
    exact (hb z hz).choose_spec.2.choose_spec
  have hcoc : ∀ z ∈ W, (hh z)⁻¹ * σ (hh z) ∈ MulAction.stabilizer G (bb z) := by
    intro z hz
    have hbW : bb z ∈ W := hB1W (bbB z hz)
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    calc σ (hh z) • bb z = σ (hh z) • s (bb z) := by rw [hfix _ hbW]
      _ = s (hh z • bb z) := (hs _ _).symm
      _ = hh z • bb z := by rw [hhb z hz, hfix z hz]
  let key : Z → Z × G := fun z => (bb z, (hh z)⁻¹ * σ (hh z))
  have hkey : (key '' W).Finite := by
    refine (hB1.prod (hB1.biUnion (fun b hbB =>
      (haveI := hstab b (hB1W hbB); Set.toFinite (MulAction.stabilizer G b : Set G))))).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨bbB z hz, Set.mem_biUnion (bbB z hz) (hcoc z hz)⟩
  obtain ⟨B, hBW, hB, hBr⟩ := fixOrb_reps key W hkey
  refine ⟨B, hB, fun z hz => ?_⟩
  obtain ⟨z', hz'B, hk⟩ := hBr z hz
  have hz'W := hBW hz'B
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨hh z' * (hh z)⁻¹, ?_, ?_⟩
  · have : σ (hh z') = hh z' * ((hh z)⁻¹ * σ (hh z)) := by
      rw [← h2, mul_inv_cancel_left]
    rw [map_mul, map_inv, this]
    group
  · rw [mul_smul, inv_smul_eq_iff.mpr (hhb z hz).symm, ← h1, hhb z' hz'W]
    exact hz'B
end

section

open UpperTheory.V.Af.BA in
theorem UpperTheory.adelic_rep_dimension_bounded :
    UpperTheory.V.Af.BA.DimBdd := by
  classical
  unfold UpperTheory.V.Af.BA.DimBdd
  intro Γ I _ _ K hfin hstab0
  have hre : ∀ {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (t : K.Tup q) (g : Γ),
      g • t = t → g • K.re f t = K.re f t := by
    intro p q f t g hg
    show K.re f (g • t) = K.re f t
    rw [hg]
  have hst : ∀ (p : ℕ) (t : K.Tup p), Finite ↥(MulAction.stabilizer Γ t) := by
    intro p t
    haveI := hstab0 (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t)
    have hle : MulAction.stabilizer Γ t ≤
        MulAction.stabilizer Γ (K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t) :=
      fun g hg => hre _ t g hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  refine ⟨hst, ?_⟩
  obtain ⟨R, hRfin, hR⟩ := hfin
  haveI : Finite ↥R := hRfin.to_subtype
  let V : K.Tup 1 → K.Tup 0 := fun r => K.re (fun _ : Fin 1 => (0 : Fin 2)) r
  haveI : ∀ r : ↥R, Finite ↥(MulAction.stabilizer Γ (V r.1)) := fun r => hstab0 _
  refine ⟨Nat.card (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))), ?_⟩
  intro p hp t ht
  let v : K.Tup 0 := K.re (fun _ : Fin 1 => (0 : Fin (p+1))) t
  let e : Fin (p+1) → K.Tup 1 := fun j => K.re (![0, j] : Fin 2 → Fin (p+1)) t
  have hev : ∀ j, V (e j) = v := fun j => Subtype.ext (funext fun _ => rfl)
  let k : ↥R → Γ := fun r => if h : ∃ g : Γ, g • v = V r.1 then Classical.choose h else 1
  let gsel : Fin (p+1) → Γ := fun j => Classical.choose (hR (e j))
  have hgsel : ∀ j, gsel j • e j ∈ R := fun j => Classical.choose_spec (hR (e j))
  let rsel : Fin (p+1) → ↥R := fun j => ⟨gsel j • e j, hgsel j⟩
  have hgv : ∀ j, gsel j • v = V (rsel j).1 := by
    intro j
    show gsel j • v = gsel j • V (e j)
    rw [hev j]
  have hk : ∀ j, k (rsel j) • v = V (rsel j).1 := by
    intro j
    have hex : ∃ g : Γ, g • v = V (rsel j).1 := ⟨gsel j, hgv j⟩
    have hkj : k (rsel j) = Classical.choose hex := dif_pos hex
    rw [hkj]
    exact Classical.choose_spec hex
  have hmem : ∀ j, gsel j * (k (rsel j))⁻¹ ∈ MulAction.stabilizer Γ (V (rsel j).1) := by
    intro j
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    have h1 : (k (rsel j))⁻¹ • V (rsel j).1 = v := by
      rw [inv_smul_eq_iff]
      exact (hk j).symm
    rw [h1, hgv j]
  let φ : Fin (p+1) → Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1)) :=
    fun j => ⟨rsel j, ⟨gsel j * (k (rsel j))⁻¹, hmem j⟩⟩
  let ψ : (Σ r : ↥R, ↥(MulAction.stabilizer Γ (V r.1))) → K.Tup 1 :=
    fun x => ((x.2 : Γ) * k x.1)⁻¹ • x.1.1
  have hψ : ∀ j, ψ (φ j) = e j := by
    intro j
    show ((gsel j * (k (rsel j))⁻¹) * k (rsel j))⁻¹ • (gsel j • e j) = e j
    rw [inv_mul_cancel_right, inv_smul_smul]
  have hinj : Function.Injective φ := by
    intro j j' hjj
    apply ht
    have h1 : e j = e j' := by rw [← hψ j, ← hψ j', hjj]
    have h2 := congrArg (fun x : K.Tup 1 => x.1 1) h1
    exact h2
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega
end

section

open CategoryTheory UpperTheory.V.Af.BA in
theorem UpperTheory.permutation_module_homology_rank :
    UpperTheory.V.Af.BA.RankHomPerm := by
  intro Γ X _ _ h
  obtain ⟨R, hR, hRx⟩ := h
  haveI := hR.fintype
  refine ⟨Fintype.card R, fun A => ?_⟩
  let Φ : (PC Γ X ⟶ A) →ₗ[ℂ] (R → A) :=
    { toFun := fun φ r => φ.hom (Finsupp.single (r : X) 1)
      map_add' := fun φ ψ => by
        ext r
        rfl
      map_smul' := fun c φ => by
        ext r
        rfl }
  have key : ∀ (χ : PC Γ X ⟶ A) (g : Γ) (x : X),
      χ.hom (Finsupp.single x 1) = A.ρ g⁻¹ (χ.hom (Finsupp.single (g • x) 1)) := by
    intro χ g x
    rw [← Rep.hom_comm_apply]
    congr 1
    show _ = permC Γ X g⁻¹ (Finsupp.single (g • x) 1)
    rw [permC_single, inv_smul_smul]
  have hinj : Function.Injective Φ := by
    intro φ ψ hφψ
    apply PC_ext
    intro x
    obtain ⟨g, hg⟩ := hRx x
    have h1 := congrFun hφψ ⟨g • x, hg⟩
    rw [key φ g x, key ψ g x]
    exact congrArg _ h1
  calc Module.rank ℂ (PC Γ X ⟶ A) ≤ Module.rank ℂ (R → A) := Φ.rank_le_of_injective hinj
    _ = _ := by rw [rank_fun_eq_lift_mul, Cardinal.lift_id]
end

section

open CategoryTheory

private theorem term_congr {G : Type} [Group G] (S : Subgroup G) (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) {g g' : G}
    (h : (g : G ⧸ S) = (g' : G ⧸ S)) : A.ρ g (F.1 g⁻¹) = A.ρ g' (F.1 g'⁻¹) := by
  have hs : g⁻¹ * g' ∈ S := QuotientGroup.eq.mp h
  let s : S := ⟨g⁻¹ * g', hs⟩
  have hF : F.1 (S.subtype s⁻¹ * g⁻¹) = (Rep.res S.subtype A).ρ s⁻¹ (F.1 g⁻¹) := F.2 s⁻¹ g⁻¹
  have hg : S.subtype s⁻¹ * g⁻¹ = g'⁻¹ := by
    show (g⁻¹ * g')⁻¹ * g⁻¹ = g'⁻¹
    group
  rw [hg] at hF
  rw [hF]
  show _ = A.ρ g' (A.ρ (g⁻¹ * g')⁻¹ (F.1 g⁻¹))
  rw [← Module.End.mul_apply, ← map_mul, show g' * (g⁻¹ * g')⁻¹ = g by group]

private noncomputable def tr {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) :
    Representation.coindV S.subtype (Rep.res S.subtype A).ρ →ₗ[ℂ] A :=
  ∑ q : G ⧸ S, A.ρ q.out ∘ₗ LinearMap.proj q.out⁻¹ ∘ₗ Submodule.subtype _

private theorem tr_apply {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A F = ∑ q : G ⧸ S, A.ρ q.out (F.1 q.out⁻¹) := by
  rw [tr, LinearMap.sum_apply]
  rfl

private theorem tr_equiv {G : Type} [Group G] (S : Subgroup G) [Fintype (G ⧸ S)] (A : Rep.{0} ℂ G) (h : G)
    (F : Representation.coindV S.subtype (Rep.res S.subtype A).ρ) :
    tr S A (Representation.coind S.subtype (Rep.res S.subtype A).ρ h F) = A.ρ h (tr S A F) := by

  rw [tr_apply, tr_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) _ _ ?_
  intro q
  have hq : ((h⁻¹ * q.out : G) : G ⧸ S) = (((MulAction.toPerm h⁻¹ : Equiv.Perm (G ⧸ S)) q).out : G) := by
    rw [QuotientGroup.out_eq']
    show _ = h⁻¹ • q
    rw [← QuotientGroup.out_eq' q, MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    rfl
  rw [← term_congr S A F hq]
  show A.ρ q.out (F.1 (q.out⁻¹ * h)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, mul_inv_rev, inv_inv]

theorem UpperTheory.coind_retract_of_finite_index :
    UpperTheory.V.Af.BA.CoindRetract := by
  classical
  unfold UpperTheory.V.Af.BA.CoindRetract
  intro G _ S hS A
  haveI := hS
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hn : (Fintype.card (G ⧸ S) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let P : A →ₗ[ℂ] Representation.coindV S.subtype (Rep.res S.subtype A).ρ :=
    { toFun := fun a => ⟨fun g => A.ρ g a, fun s g => by
        show A.ρ (S.subtype s * g) a = A.ρ (S.subtype s) (A.ρ g a)
        rw [map_mul, Module.End.mul_apply]⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add (A.ρ g) a b)
      map_smul' := fun c a => Subtype.ext (funext fun g => map_smul (A.ρ g) c a) }
  let π : A ⟶ Rep.coind S.subtype (Rep.res S.subtype A) :=
    Rep.ofHom ⟨P, fun h => LinearMap.ext fun a => Subtype.ext (funext fun g => by
      show A.ρ g (A.ρ h a) = A.ρ (g * h) a
      rw [map_mul, Module.End.mul_apply])⟩
  let ι : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A :=
    Rep.ofHom ⟨(Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A, fun h => LinearMap.ext fun F => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
      exact congrArg (fun x => (Fintype.card (G ⧸ S) : ℂ)⁻¹ • x) (tr_equiv S A h F)⟩
  refine ⟨π, ι, ?_⟩
  apply Rep.hom_ext
  ext a
  show (Fintype.card (G ⧸ S) : ℂ)⁻¹ • tr S A (P a) = a
  rw [tr_apply]
  have hterm : ∀ q : G ⧸ S, A.ρ q.out ((P a).1 q.out⁻¹) = a := fun q => by
    show A.ρ q.out (A.ρ q.out⁻¹ a) = a
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
end

section

open NumberField Pointwise UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA

private theorem minVec_smul' {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gm L N) (h : HS L N) :
    minVec (g • h) = g • minVec h := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp [minVec, q_smul]

private theorem vert_ext' {L : Type} [Field L] [NumberField L] {N : ℕ} (a b : ↥(HR L N))
    (ha : ConeExtensionAcyclic.IsVert (qr L N) a) (e : minVec a.1 = minVec b.1) : a = b := by
  have : a - b = 0 := ha.2 _ fun y hy => by
    have h1 : y.1 ∈ minVec a.1 := hy
    rw [e] at h1
    have h2 : qr L N y b = 1 := h1
    rw [map_sub, hy, h2, sub_self]
  exact sub_eq_zero.1 this

theorem UpperTheory.orbRe_of_minimal_vector_stabilizer :
    UpperTheory.V.Af.BA.FixOrb → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.MinOrb → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.OrbRe := by
  intro hFix hInv hAct hSpan hOrb hStab L _ _ _ N σ hσ p
  obtain ⟨hinv, hre⟩ := hInv L N σ hσ
  obtain ⟨inst, hval, -⟩ := hAct L N σ hσ
  have hRy : ∀ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 ∈ Ry L N := fun v y hy => v.2.1 ⟨y, hy⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := hOrb L N p
  obtain ⟨R₀, hR₀, hR₀'⟩ := hFix (Gm L N) (Fin (p + 1) → Set (Lat L N)) (sGm N σ)
    (fun z j => sLat σ '' z j)
    (fun g z => by
      funext j
      change sLat σ '' ((fun y => g • y) '' z j) = (fun y => sGm N σ g • y) '' (sLat σ '' z j)
      simp only [Set.image_image, sLat_smul])
    {z | ∃ t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) (p + 1), z = fun j => minVec (t j).1.1}
    (by
      rintro _ ⟨t, -, rfl⟩
      funext j
      ext y
      have hq := (hre _ (t j).1.2).1
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hq x).trans hx
      · intro hy
        exact ⟨sLat σ y, (hq y).trans hy, funext fun a => hinv _⟩)
    (by
      rintro _ ⟨t, ht, rfl⟩
      have hs : Spans (minVec (t 0).1.1) := by
        have := hSpan L N σ hσ p t ht
        unfold Spans spanL at *
        refine top_le_iff.1 (this ▸ Submodule.span_mono (Set.image_mono fun y hy => hy 0))
      haveI := hStab L N _ (hRy (t 0)) hs
      have hle : MulAction.stabilizer (Gm L N) (fun j => minVec (t j).1.1) ≤
          MulAction.stabilizer (Gm L N) (minVec (t 0).1.1) := fun g hg => congrFun hg 0
      exact Finite.of_injective _ (Subgroup.inclusion_injective hle))
    ⟨R₁, hR₁, by
      rintro _ ⟨t, ht, rfl⟩
      exact hR₁' (fun j => (t j).1.1) (fun j => hRy _) (hSpan L N σ hσ p t ht)⟩
  refine ⟨{h | (∀ j, ∃ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 = h j) ∧ (fun j => minVec (h j)) ∈ R₀}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun h j => minVec (h j)) (hR₀.subset ?_) ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact hh.2
    · intro a ha b hb e
      funext j
      obtain ⟨v, hv⟩ := ha.1 j
      obtain ⟨w, hw⟩ := hb.1 j
      have ej : minVec (a j) = minVec (b j) := congrFun e j
      rw [← hv, ← hw] at ej ⊢
      rw [vert_ext' _ _ v.2 ej]
  · intro t ht
    obtain ⟨g, hg, hgR⟩ := hR₀' _ ⟨t, ht, rfl⟩
    refine ⟨g, hg, fun j => ⟨(⟨g, hg⟩ : ↥(Fix N σ)) • t j, hval _ _⟩, ?_⟩
    simp only [minVec_smul']
    exact hgR
end

section

private theorem UpperTheory.cardinal_sum_eq_finite_sum_range (N : ℕ) : ∀ f : ℕ → Cardinal.{0}, (∀ q, N ≤ q → f q = 0) →
    Cardinal.sum f = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero =>
    intro f hf
    have hf0 : f = fun _ => 0 := funext fun q => hf q (Nat.zero_le q)
    subst hf0
    rw [Cardinal.sum_const', mul_zero, Finset.sum_range_zero]
  | succ N ih =>
    intro f hf
    rw [Cardinal.sum_nat_eq_add_sum_succ, ih (fun i => f (i+1)) (fun q hq => hf (q+1) (by omega)),
      Finset.sum_range_succ', add_comm]

theorem UpperTheory.adelic_rep_bounded_of_degree_bounded :
    UpperTheory.V.Af.BA.BddOfDeg := by
  unfold UpperTheory.V.Af.BA.BddOfDeg
  intro Γ _ hc hD
  choose c hc using hc
  obtain ⟨D, hD⟩ := hD
  unfold UpperTheory.V.Af.CohB.Bdd
  refine ⟨∑ q ∈ Finset.range D, c q, fun A => ?_⟩
  unfold UpperTheory.V.Af.CohB.totCoh
  rw [UpperTheory.cardinal_sum_eq_finite_sum_range D _ (fun q hq => hD q hq A), Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun q _ => hc q A
end
