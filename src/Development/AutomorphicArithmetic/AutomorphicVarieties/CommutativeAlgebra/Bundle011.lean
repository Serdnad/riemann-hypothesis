module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle005
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle003
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
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chart_add_coeff {K τ τ' : Type} [CommRing K] (ε : τ ≃ τ') (p : MvPowerSeries τ K) (n : τ' →₀ ℕ) :
    coeff n (rename ε p) = coeff (Finsupp.mapDomain ε.symm n) p := by
  have h := coeff_embDomain_rename ε.toEmbedding p (Finsupp.mapDomain ε.symm n)
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp] at h
  have h2 : (ε.toEmbedding : τ → τ') ∘ ε.symm = id := funext fun x => ε.apply_symm_apply x
  rw [h2, Finsupp.mapDomain_id] at h
  exact h

private theorem chart_add_weight {τ τ' X : Type} [AddCommGroup X] (g : τ' → τ) (wt : τ → X) (n : τ' →₀ ℕ) :
    Finsupp.weight wt (Finsupp.mapDomain g n) = Finsupp.weight (fun s => wt (g s)) n := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a b => simp [Finsupp.weight_single]

private theorem chart_add_rename {O A X τ τ' : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    [AddCommGroup X] {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (ε : τ ≃ τ') (wt' : τ' → X)
    (hw : ∀ s, wt' s = wt (ε.symm s)) :
    IsChart 𝒜 x wt' (((rename ε).restrictScalars O).comp φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf n hn
    show coeff n (rename ε (φ f)) = 0
    rw [chart_add_coeff]
    refine h.graded j f hf _ ?_
    rwa [chart_add_weight, ← funext hw]
  · intro f
    show constantCoeff (rename ε (φ f)) = _
    rw [constantCoeff_rename, h.const]
  · intro i
    obtain ⟨f, h1, h2⟩ := h.onto (ε.symm i)
    refine ⟨f, ?_, fun i' hi' => ?_⟩
    · show coeff _ (rename ε (φ f)) ≠ 0
      rwa [chart_add_coeff, Finsupp.mapDomain_single]
    · show coeff _ (rename ε (φ f)) = 0
      rw [chart_add_coeff, Finsupp.mapDomain_single]
      exact h2 _ fun h3 => hi' (ε.symm.injective h3)
  · intro f hx hf
    refine h.inj f hx fun i => ?_
    have h1 : coeff _ (rename ε (φ f)) = 0 := hf (ε i)
    rwa [chart_add_coeff, Finsupp.mapDomain_single, ε.symm_apply_apply] at h1

private def chart_add_equiv (F : Bool → Type) : (Σ v, F v) ≃ F true ⊕ F false where
  toFun
    | ⟨true, s⟩ => .inl s
    | ⟨false, s⟩ => .inr s
  invFun
    | .inl s => ⟨true, s⟩
    | .inr s => ⟨false, s⟩
  left_inv
    | ⟨true, _⟩ => rfl
    | ⟨false, _⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

private def chart_add_fam (A B : Type) : Bool → Type := fun v => Bool.rec B A v

theorem UpperTheory.V.Alg.chart_add :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (W' : WPres O X R') (τ' : Type) [Fintype τ'] (e : W.σ ⊕ τ' ≃ W'.σ), (∀ s, W'.wt (e (.inl s)) = W.wt s) →
      RingHom.ker W'.π = (RingHom.ker W.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
      ∃ (h' : W'.HasOrigin) (ψ : R' →ₐ[O] MvPowerSeries (τ ⊕ τ') (FractionRing O)), IsChart W'.part (W'.origin h') (Sum.elim wt fun s => W'.wt (e (.inr s))) ψ ∧
        (∀ s, ψ (W'.z (e (.inl s))) = MvPowerSeries.rename Sum.inl (φ (W.z s))) ∧ ∀ s, ψ (W'.z (e (.inr s))) = MvPowerSeries.X (.inr s) := by
  intro O X R _ _ _ _ iR aR W h τ fτ wt φ hφ R' _ _ W' τ' fτ' e hwt hker
  let W0 : WPres O X (MvPowerSeries τ' O) := WPres.free O fun s : τ' => W'.wt (e (.inr s))
  have h0 : W0.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  obtain ⟨φ0, hφ0, hz0⟩ := chart_free O X (MvPowerSeries τ' O) W0 h0 Function.injective_id
  let B : Bool → Type := chart_add_fam R (MvPowerSeries τ' O)
  letI iB : ∀ v : Bool, CommRing (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => CommRing (B v)) (inferInstance : CommRing (MvPowerSeries τ' O)) iR v
  letI aB : ∀ v : Bool, Algebra O (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => @Algebra O (B v) _ (iB v).toCommSemiring.toSemiring) (inferInstance : Algebra O (MvPowerSeries τ' O)) aR v
  let WB : ∀ v : Bool, WPres O X (B v) := fun v => Bool.rec (motive := fun v : Bool => WPres O X (B v)) W0 W v
  have hB : ∀ v : Bool, (WB v).HasOrigin := fun v => Bool.rec (motive := fun v : Bool => (WB v).HasOrigin) h0 h v
  let F : Bool → Type := chart_add_fam τ τ'
  letI fF : ∀ v : Bool, Fintype (F v) := fun v => Bool.rec (motive := fun v : Bool => Fintype (F v)) fτ' fτ v
  let wF : ∀ v : Bool, F v → X := fun v => Bool.rec (motive := fun v : Bool => F v → X) W0.wt wt v
  let φF : ∀ v : Bool, B v →ₐ[O] MvPowerSeries (F v) (FractionRing O) := fun v =>
    Bool.rec (motive := fun v : Bool => B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)) φ0 φ v
  have hF : ∀ v : Bool, IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v) := fun v =>
    Bool.rec (motive := fun v : Bool => IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)) hφ0 hφ v
  let e' : (Σ v, (WB v).σ) ≃ W'.σ := (chart_add_equiv fun v => (WB v).σ).trans e
  obtain ⟨h', ψ, hψ, hz⟩ := chart_sum O X Bool B WB hB F wF φF hF R' W' e'
    (fun v => Bool.rec (motive := fun v : Bool => ∀ s, W'.wt (e' ⟨v, s⟩) = (WB v).wt s) (fun _ => rfl) hwt v) (by
      rw [iSup_bool_eq, hker]
      have h1 : RingHom.ker (WB false).π = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
      rw [h1, Ideal.map_bot, sup_bot_eq]
      rfl)
  let ε : (Σ v, F v) ≃ τ ⊕ τ' := chart_add_equiv F
  refine ⟨h', ((rename ε).restrictScalars O).comp ψ, chart_add_rename hψ ε _ ?_, fun s => ?_, fun s => ?_⟩
  · rintro (s | s) <;> rfl
  · have h1 := congrArg (rename ε) (hz true s)
    rw [rename_rename] at h1
    exact h1
  · have h1 := congrArg (rename ε) (hz false s)
    rw [rename_rename] at h1
    refine h1.trans ?_
    have h2 : φF false ((WB false).z s) = MvPowerSeries.X s := hz0 s
    rw [h2]
    exact rename_X _ _
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {X : Type} [AddCommGroup X]

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma π_monomial (W : WPres O X R) (m : W.σ →₀ ℕ) :
    W.π (monomial m 1) = m.prod fun i k => W.z i ^ k := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
  simp [WPres.z]

private lemma z_mem_ker (W : WPres O X R) (h : W.HasOrigin) (i : W.σ) : W.z i ∈ RingHom.ker (W.origin h) := by
  rw [RingHom.mem_ker, WPres.z, W.origin_π]
  simp

private lemma deg_lt_two {σ : Type} (m : σ →₀ ℕ) (hm : m.degree < 2) :
    m = 0 ∨ ∃ s, m = Finsupp.single s 1 := by
  rcases (by omega : m.degree = 0 ∨ m.degree = 1) with h | h
  · exact Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)
  · right
    obtain ⟨s, hs⟩ := (Finsupp.sum_eq_one_iff m).1 (by rw [← h, Finsupp.degree_apply]; rfl)
    exact ⟨s, hs⟩

private lemma sq_mem [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) (j : X)
    (g : MvPowerSeries W.σ O) (hg : ∀ m, ¬ (Finsupp.weight W.wt m = j ∧ 2 ≤ m.degree) → coeff m g = 0)
    (y : W.A) (hy : W.π g = (y : R)) : y ∈ RingHom.ker (W.originA h) ^ 2 := by
  obtain ⟨μ, hμ, hs⟩ := part_span O R X W {m | Finsupp.weight W.wt m = j ∧ 2 ≤ m.degree} j (fun _ hm => hm.1)
  obtain ⟨b, hb, hbs⟩ := hs g hg
  have h3 : y = ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k := by
    apply Subtype.ext

    rw [← hy, hbs, map_sum]
    simp [π_monomial, Finsupp.prod, WPres.zA]
  rw [h3]
  exact Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _
    (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)

end

theorem UpperTheory.V.Alg.cot_fg :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (j : X), cotLat (W.originA h) W.gr j = cotSpan (W.originA h) fun s : {s // W.wt s = j} => W.zA s := by
  intro O X R _ _ _ _ _ _ W h _ _ j
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨⟨f, hf, hfx⟩, hx⟩, rfl⟩
    have hfx' : W.π f = (x : R) := hfx
    have h0 : constantCoeff f = 0 := by
      rw [← W.origin_π h, hfx']
      exact hx
    have key : x - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s ∈
        RingHom.ker (W.originA h) ^ 2 := by
      refine sq_mem W h j (f - ∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • MvPowerSeries.X s.1)
        (fun m hm => ?_) _ (by simp [hfx', WPres.zA, WPres.z])

      rw [map_sub, map_sum]
      simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hw : Finsupp.weight W.wt m = j
      · rcases deg_lt_two m (not_le.1 fun h2 => hm ⟨hw, h2⟩) with rfl | ⟨s, rfl⟩
        · rw [Finset.sum_eq_zero fun s _ => if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
          simpa using h0
        · have hs : W.wt s = j := by simpa [Finsupp.weight_single] using hw
          rw [Finset.sum_eq_single (⟨s, hs⟩ : {s // W.wt s = j}), if_pos rfl, sub_self]
          · intro t _ ht
            rw [if_neg]
            intro h2
            exact ht (Subtype.ext (Finsupp.single_left_injective one_ne_zero h2).symm)
          · simp
      · rw [hf m hw, Finset.sum_eq_zero, sub_self]
        intro s _
        rw [if_neg]
        rintro rfl
        exact hw (by simpa [Finsupp.weight_single] using s.2)
    have h2 : (satSq (W.originA h)).mkQ x = (satSq (W.originA h)).mkQ
        (∑ s : {s // W.wt s = j}, coeff (Finsupp.single s.1 1) f • W.zA s) :=
      (Submodule.Quotient.eq _).2 ⟨1, one_ne_zero, by rwa [one_smul]⟩

    rw [h2, map_sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s, rfl⟩, rfl⟩
    exact ⟨W.zA s, ⟨W.z_mem s, z_mem_ker W h s⟩, rfl⟩
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A ι : Type} [CommRing k] [CommRing A] [Fintype ι] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : Matrix ι ι k →+ Matrix ι ι A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : Matrix ι ι A) Y, M * T Y = T (M.map π * Y)) ∧
      ∀ (M : Matrix ι ι A) Y, T Y * M = T (Y * M.map π) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_⟩
  · ext a b

    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b

    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]

private theorem rbar_lc {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] (r : Lift O rbar R) : IsLocallyConstant fun s => rbar s := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rbar t a b = rbar s a b := fun a b => by
    filter_upwards [(r.cont a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff O, map_sub, r.red, r.red, sub_eq_zero] at ht
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Alg.obs_correct :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) →
          ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ →
          ∀ (μ : ResidueField O → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res O A a * c) = a * μ c) → (∀ c, p (μ c) = 0) →
          ∀ (i : B →ₐ[O] A) (r : Lift O rbar R) (rt : Γ → Matrix ι ι A), (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) → (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) → (∀ s, (rt s).map p = r.hom s) →
          ∀ (α : F.T → Matrix ι ι A), (∀ v, Φ.HH (α v)) → α F.v0 = 1 →
          ∀ (rq : ∀ q, Lift O (rbar.comp (F.ψ q)) A), (∀ q, Φ.InH (r0.hom.comp (F.ψ q)) A (rq q)) → (∀ q, L q A (rq q)) → (∀ q, (rq q).map p = r.comap (F.ψ q) (F.hψ q)) →
          ∀ (j : X), ∀ x ∈ F.framedTwoCoboundaries (FormData.adRep hbar j), (∀ s t, rt s * rt t - rt (s * t) = ((x.1 (s, t)).1 * rbar (s * t)).map μ) → (∀ v s, rt (F.φ v s) * α v - α v * ((ρ v).hom s).map i = ((x.2.1 v s).1 * rbar (F.φ v s)).map μ) → (∀ q s, rt (F.ψ q s) - (rq q).hom s = ((x.2.2 q s).1 * rbar (F.ψ q s)).map μ) →
          ∃ (r' : Lift O rbar A) (α' : F.T → Matrix ι ι A), IsFramed Φ r0.hom F L ρ i r' α' ∧ r'.map p = r ∧ ∀ v, (α' v).map p = (α v).map p := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F L hN hL B _ _ _ ρ A _ _ _ R _ _ _ p hp hs μ m1 m2 m3
    i r rt t1 t2 t3 α a1 a2 rq q1 q2 q3 j x hx x1 x2 x3
  obtain ⟨T, T0, Tl, Tr⟩ := exists_strictHenselian_absolutely_closed_local_ring (ι := ι) (res O A) μ m1 m2
  simp only [T0] at x1 x2 x3
  have lc := rbar_lc r0
  have ad : ∀ s (Y : Φ.gw (ResidueField O) j), (FormData.adRep hbar j s Y).1 = rbar s * Y.1 * rbar s⁻¹ :=
    fun _ _ => rfl
  obtain ⟨h, y, b1, b2, b3, b4, b5⟩ := cocycle_normal_form _ _ _ F (FormData.adRep hbar j) (fun m => by
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      exact (lc.comp (· * m.1)).mul (lc.comp_continuous continuous_inv))
    (fun q n hn m => Subtype.ext (by
      rw [ad, ← map_inv, hN q n hn, hN q _ (inv_mem hn), one_mul, mul_one])) x hx
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res O A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res O A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (rt s).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← r.red, ← t3, Matrix.map_apply]
  have r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, ← r0.red]
    exact res_map (Algebra.ofId O A) _
  have ρres : ∀ v s, (((ρ v).hom s).map i).map (res O A) = rbar (F.φ v s) := fun v s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, res_map, (ρ v).red]
    rfl
  have Jres : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have Tg : ∀ Y : Φ.gw (ResidueField O) j, T Y.1 ∈ Φ.g A := fun Y => by
    obtain ⟨⟨y1, y2⟩, -⟩ := Y.2
    refine ⟨?_, fun a b e => ?_⟩
    · have : (T Y.1).transpose = T Y.1.transpose := by rw [← T0, ← T0, Matrix.transpose_map]
      rw [this, Tl, Tr, Jres, ← map_add (f := _), y1, map_zero]
    · have : T 0 a b = 0 := by rw [map_zero]; rfl
      rw [← T0, Matrix.map_apply, y2 a b e, ← this, ← T0]
      rfl
  obtain ⟨-, -, s3⟩ := hh_small O ι X w Φ h2 A R p hp hs
  obtain ⟨-, -, g3, -⟩ := hh_group O ι X w Φ A
  have inv1 : ∀ s, rbar s * rbar s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → Matrix ι ι A := fun s => rt s - T ((h s).1 * rbar s) with hf
  have fH : ∀ s, Φ.HH (f s * (r0.hom s⁻¹).map (algebraMap O A)) := fun s => by
    have := s3 _ _ (t1 s) (Tg (-h s)) (Tp _)
    rw [hf]
    simp only
    rw [sub_mul, Tr, r0res, mul_assoc, inv1, mul_one, sub_eq_add_neg, ← map_neg]
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (FormData.adRep hbar j) h (s, t)).1 : Matrix ι ι _) * rbar (s * t) =
        (h s).1 * rbar s * rbar t + rbar s * ((h t).1 * rbar t) - (h (s * t)).1 * rbar (s * t) := by
      show ((h s).1 + rbar s * (h t).1 * rbar s⁻¹ - (h (s * t)).1) * rbar (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rbar s * (h t).1), ← mul_assoc (rbar s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add (f := _)]
    abel
  have fone : f 1 = 1 := by
    obtain ⟨u, -, hu, -⟩ := g3 _ (fH 1)
    rw [inv_one, map_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at hu
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = f 1 * (f 1 * u) := by rw [hu, mul_one]
      _ = 1 := by rw [← mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r.hom s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, t3, sub_zero]
  let r' : Lift O rbar A :=
    { hom := { toFun := f, map_one' := fone, map_mul' := fmul }
      cont := fun a b N => by
        have c1 := t2 a b N
        have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rbar s) a b) :=
          ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
        have c3 := c1.sub c2
        convert c3 using 2 with s
        exact map_sub _ _ _
      red := fun s a b => by
        have := congrFun (congrFun (fp s) a) b
        rw [← r.red, ← this, Matrix.map_apply, res_map]
        rfl }
  have r'p : r'.map p = r := by
    ext s a b
    exact congrFun (congrFun (fp s) a) b
  refine ⟨r', fun v => α v + T (y v).1, ⟨fH, fun q => ?_, fun v => s3 _ _ (a1 v) (Tg _) (Tp _), ?_, fun v s => ?_⟩,
    r'p, fun v => ?_⟩
  · refine ((hL q).tangent A R p hp hs (rq q) (r'.comap (F.ψ q) (F.hψ q)) (q1 q) (fun s => ?_) ?_ (q2 q)).2
      fun n hn => ?_
    · have := fH (F.ψ q s)
      rw [← map_inv] at this
      exact this
    · rw [q3, ← r'p]
      rfl
    · have e := x3 q n
      rw [b5 q n hn] at e
      show rt (F.ψ q n) - T _ = _
      rw [← e, sub_sub_cancel]
  · simp only [a2, b2]
    simp
  · have e := x2 v s
    rw [b4, sub_eq_iff_eq_add] at e
    have e' : ((h (F.φ v s) - (FormData.adRep hbar j (F.φ v s) (y v) - y v)).1 : Matrix ι ι _) * rbar (F.φ v s) =
        (h (F.φ v s)).1 * rbar (F.φ v s) - (rbar (F.φ v s) * (y v).1 - (y v).1 * rbar (F.φ v s)) := by
      show ((h (F.φ v s)).1 - (rbar (F.φ v s) * (y v).1 * rbar (F.φ v s)⁻¹ - (y v).1)) * rbar (F.φ v s) = _
      rw [sub_mul, sub_mul, mul_assoc, inv2, mul_one]
    show (rt (F.φ v s) - T _) * (α v + T _) = (α v + T _) * _
    rw [sub_mul, mul_add, mul_add, add_mul, TT, Tl, Tr, Tr, rtres, ρres, (a1 v).2.2, mul_one, e, e', map_sub, map_sub]
    abel
  · show (α v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero]
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_mvps_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsAdicComplete (maximalIdeal A) A) :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

private theorem co_mvps_fin (R : Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact co_mvps_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm inferInstance
  | succ n ih =>
    exact co_mvps_equiv (finSuccEquiv R n).toRingEquiv.symm
      (UpperTheory.V.abelian₂.adicComplete (MvPowerSeries (Fin n) R))

theorem UpperTheory.V.Alg.co_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ], IsCO O (MvPowerSeries σ R) := by
  intro O _ _ R _ _ hR σ _
  have hc : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherian := MvPowerSeries.isNoetherianRing R
      complete := co_mvps_equiv (renameEquiv R e.symm).toRingEquiv (co_mvps_fin R n)
      isLocalHom := ⟨fun a ha => ?_⟩
      res_surj := fun x => ?_ }
  · have h := isUnit_constantCoeff _ ha
    rw [MvPowerSeries.algebraMap_apply, constantCoeff_C] at h
    exact IsLocalHom.map_nonunit a h
  · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (constantCoeff x)
    refine ⟨a, fun h => ha ?_⟩
    have h2 := isUnit_constantCoeff _ h
    rwa [map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C] at h2
end
