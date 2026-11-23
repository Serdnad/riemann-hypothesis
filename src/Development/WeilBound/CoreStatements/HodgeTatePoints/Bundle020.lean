module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle077
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle014
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem eigQuot_lattice {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {E : Type} [Field E] [NumberField E]
    {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (ρ : 𝓞 E →+* Module.End C Ω) (σ : E →+* C) (X : Submodule O Ω) (hX : X.IsLattice C) :
    (latIn (eigQuot ρ σ X) (eigSp ρ σ)).IsLattice C := by
  let f : Ω →ₗ[O] eigSp ρ σ :=
    ((eigProj ρ σ).codRestrict (eigSp ρ σ) (LatBasic.eigProj_mem ρ σ)).restrictScalars O
  have hmap : latIn (eigQuot ρ σ X) (eigSp ρ σ) = X.map f := by
    ext x
    change (∃ y ∈ X, eigProj ρ σ y = (x : Ω)) ↔ ∃ y ∈ X, f y = x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, Subtype.ext h⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, congrArg Subtype.val h⟩
  haveI : IsFractionRing O C := hv.isFractionRing
  rw [hmap]
  exact Submodule.IsLattice.of_fg C (hX.fg.map f)

theorem pt_om_block : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C), P.omHT σ ≤ P.omRec σ ∧ (∀ x ∈ P.omRec σ, κ • x ∈ P.omHT σ) ∧ (latIn (P.omHT σ) (P.Ωsp σ)).IsLattice C ∧ (latIn (P.omRec σ) (P.Ωsp σ)).IsLattice C := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ
  refine ⟨Submodule.map_mono ?_, ?_, eigQuot_lattice hv _ _ _ (PtBasic.om'_lattice P),
    eigQuot_lattice hv _ _ _ P.om_lat.toIsLattice⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, e⟩ := P.κ_mem y hy
    exact ⟨κ • y, ⟨x, hx, e⟩, map_smul _ _ _⟩

section

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem e_eigProj (hc : ∀ x, c (c x) = x) (σ : E →+* C) {x : V} (hx : x ∈ eigSp P.ρ σ) (y : V) :
    P.e x (eigProj P.ρ (σ.comp c.toRingHom) y) = P.e x y := by
  have h : ∀ a : 𝓞 E, P.e x (P.ρ a y) = σ (c (a : E)) * P.e x y := by
    intro a
    have h1 := P.adj (RingOfIntegers.mapRingEquiv c a) x y
    have h2 : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      ext; exact hc _
    rw [h2, LatBasic.mem_eigSp.1 hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact h1.symm

  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_eq_mul,
  ← mul_assoc]
  rw [← Finset.sum_mul]
  have : ∑ k, (σ.comp c.toRingHom) (dualInt E k) * σ (c ((RingOfIntegers.basis E k : 𝓞 E) : E)) = 1 := by

    rw [← map_one (σ.comp c.toRingHom), ← LatBasic.sum_dualInt_mul, map_sum]
    simp
  rw [this, one_mul]

theorem finrank_eigSp [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (eigSp P.ρ σ) = N := by
  obtain ⟨h1, d, -, -, h2⟩ := exists_diff_generator C v O hv E σ
  obtain ⟨-, -, h3, h4⟩ := SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d
    hv.hom_inj h1 h2 P.free
  rw [← h4, finrank_span_eq_card h3, Fintype.card_fin]

theorem finrank_W_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Ωsp σ) = N := by
  haveI := PtBasic.finite_V P
  let f := P.ht ∘ₗ (eigSp P.ρ σ).subtype
  have h := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = P.Ωsp σ := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change P.ht x ∈ eigSp _ _
      rw [← LatBasic.eigProj_of_mem x.2, PtBasic.ht_eigProj]
      exact LatBasic.eigProj_mem _ _ _
    · intro y hy
      obtain ⟨x, rfl⟩ := PtBasic.ht_surjective P y
      refine ⟨⟨_, LatBasic.eigProj_mem P.ρ σ x⟩, ?_⟩
      change P.ht (eigProj P.ρ σ x) = _
      rw [PtBasic.ht_eigProj, LatBasic.eigProj_of_mem hy]
  have hk : finrank C (LinearMap.ker f) = finrank C (P.Wsp σ) := by
    rw [← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype,
      inf_comm]
    rfl
  rw [hr, hk, finrank_eigSp P hv] at h
  omega

theorem finrank_W_add_conj [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Wsp σ) + finrank C (P.Wsp (σ.comp c.toRingHom)) = N := by
  haveI := PtBasic.finite_V P
  set τ := σ.comp c.toRingHom
  let B : eigSp P.ρ σ →ₗ[C] Module.Dual C (eigSp P.ρ τ) :=
    (P.e.domRestrict₁₂ (eigSp P.ρ σ) (eigSp P.ρ τ))
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have : (x : V) = 0 := P.nondeg _ fun y => by
      rw [PtBasic.e_skew, ← e_eigProj P hc σ x.2, neg_eq_zero]
      exact congrArg (fun φ => φ ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩) (LinearMap.mem_ker.1 hx)
    exact Subtype.ext this
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Subspace.dual_finrank_eq, finrank_eigSp P hv, finrank_eigSp P hv])).1 hinj
  let W₁ : Submodule C (eigSp P.ρ σ) := P.W.comap (eigSp P.ρ σ).subtype
  let W₂ : Submodule C (eigSp P.ρ τ) := P.W.comap (eigSp P.ρ τ).subtype
  have hW : W₁ = W₂.dualAnnihilator.comap B := by
    ext x
    rw [Submodule.mem_comap (f := B), Submodule.mem_dualAnnihilator]
    change P.ht x = 0 ↔ _
    rw [P.lagr]
    refine ⟨fun h w hw => h w hw, fun h y hy => ?_⟩
    rw [← e_eigProj P hc σ x.2]
    refine h ⟨_, LatBasic.eigProj_mem P.ρ τ y⟩ ?_
    change P.ht (eigProj P.ρ τ y) = 0
    rw [PtBasic.ht_eigProj, hy, map_zero]
  have e1 : finrank C W₁ = finrank C W₂.dualAnnihilator := by
    rw [← (LinearEquiv.ofBijective B ⟨hinj, hsurj⟩).finrank_map_eq W₁, hW]
    exact congrArg (fun U : Submodule C (Module.Dual C (eigSp P.ρ τ)) => finrank C U)
      (Submodule.map_comap_eq_of_surjective hsurj _)
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W₂
  have e3 : ∀ s : E →+* C, finrank C (P.W.comap (eigSp P.ρ s).subtype) = finrank C (P.Wsp s) := by
    intro s
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]
    rfl
  rw [← e1, finrank_eigSp P hv, e3, e3] at e2
  omega

theorem finrank_Ω_add_Ω [CharZero C] {v : Valuation C NNReal} (hv : v.Integers O)
    (hc : ∀ x, c (c x) = x) (σ : E →+* C) :
    finrank C (P.Ωsp σ) + finrank C (P.Ωsp (σ.comp c.toRingHom)) = N := by
  have h1 := finrank_W_add_Ω P hv σ
  have h2 := finrank_W_add_Ω P hv (σ.comp c.toRingHom)
  have h3 := finrank_W_add_conj P hv hc σ
  omega

end

end PositivityTheory.HtPt.Gb
end
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

section Loc
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def loc (B : Subalgebra o Ω) (u : Ω) (hu : u ∈ B) : Subring Ω where
  carrier := {a | ∃ n : ℕ, u ^ n * a ∈ B}
  one_mem' := ⟨0, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [mul_neg]; exact neg_mem h⟩
  mul_mem' := fun ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := mul_mem h h'
    rwa [mul_mul_mul_comm, ← pow_add] at this⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (mul_mem (pow_mem hu n') h) (mul_mem (pow_mem hu n) h')
    convert this using 1
    ring⟩

variable {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}

theorem loc_of_mem {a : Ω} (h : a ∈ B) : a ∈ loc B u hu := ⟨0, by simpa using h⟩

theorem loc_ev {a : Ω} (h : a ∈ loc B u hu) : ∀ᶠ n in atTop, u ^ n * a ∈ B := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := mul_mem (pow_mem hu d) h
  convert this using 1
  ring

theorem loc_of_pow {a : Ω} (n : ℕ) (h : u ^ n * a ∈ loc B u hu) : a ∈ loc B u hu := by
  obtain ⟨m, h⟩ := h
  exact ⟨m + n, by rwa [pow_add, mul_assoc]⟩

variable {V : Type} [AddCommGroup V] [Module Ω V]

def locM (M : Submodule B V) (u : Ω) (hu : u ∈ B) : AddSubgroup V where
  carrier := {v | ∃ n : ℕ, u ^ n • v ∈ M}
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [smul_neg]; exact neg_mem h⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (M.smul_mem ⟨_, pow_mem hu n'⟩ h) (M.smul_mem ⟨_, pow_mem hu n⟩ h')
    simp only [Subalgebra.smul_def, smul_smul, ← pow_add] at this
    rwa [smul_add, add_comm n' n] at *⟩

theorem locM_smul {M : Submodule B V} {a : Ω} {v : V} (ha : a ∈ loc B u hu) (hv : v ∈ locM M u hu) :
    a • v ∈ locM M u hu := by
  obtain ⟨n, h⟩ := ha
  obtain ⟨n', h'⟩ := hv
  refine ⟨n + n', ?_⟩
  have := M.smul_mem ⟨_, h⟩ h'
  simp only [Subalgebra.smul_def, smul_smul] at this ⊢
  convert this using 2
  ring

theorem locM_ev {M : Submodule B V} {v : V} (h : v ∈ locM M u hu) : ∀ᶠ n in atTop, u ^ n • v ∈ M := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := M.smul_mem ⟨_, pow_mem hu d⟩ h
  simp only [Subalgebra.smul_def, smul_smul] at this
  rwa [add_comm, pow_add]

theorem coef_mem [IsFractionRing B Ω] {P : Type} [AddCommGroup P] [Module B P] (ι : P →ₗ[B] V)
    (hι : Function.Injective ι) {k : ℕ} (b : Basis (Fin k) B P) (T : Fin k → Ω) (n : ℕ) (x : P)
    (e : u ^ n • ∑ a, T a • ι (b a) = ι x) (a : Fin k) : T a ∈ loc B u hu := by
  have h1 : LinearIndependent Ω (fun a => ι (b a)) :=
    (LinearIndependent.iff_fractionRing B Ω).1 (b.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι))
  have h2 : ∑ a, (u ^ n * T a - (b.repr x a : Ω)) • ι (b a) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, e]
    have := congrArg ι (b.sum_repr x)

    simp only [map_sum, map_smul, Subalgebra.smul_def] at this
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 h1 _ h2 a
  exact ⟨n, by rw [sub_eq_zero.1 this]; exact (b.repr x a).2⟩

theorem coef_mem_dual [IsFractionRing B Ω] (W : Submodule B V) (hW : W.FG) {j : ℕ}
    (b : Basis (Fin j) B (Dual B W)) (φ : Fin j → Dual Ω V) (hφ : ∀ a (z : W), (b a z : Ω) = φ a z)
    (T : Fin j → Ω) (h : ∀ z ∈ W, (∑ a, T a • φ a) z ∈ loc B u hu) (a : Fin j) : T a ∈ loc B u hu := by
  set ψ := ∑ a, T a • φ a with hψ
  obtain ⟨S, hS⟩ := hW
  obtain ⟨n, hn⟩ := ((eventually_all_finset S).2 fun z hz =>
    loc_ev (h z (hS ▸ Submodule.subset_span hz))).exists
  have hn' : ∀ z ∈ W, u ^ n * ψ z ∈ B := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hn x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]; exact mul_mem c.2 hx
  let x : Dual B W :=
    { toFun := fun z => ⟨_, hn' z z.2⟩
      map_add' := fun z z' => Subtype.ext (by simp [mul_add])
      map_smul' := fun c z => Subtype.ext (by simp [Subalgebra.smul_def, mul_left_comm]) }
  let ι : Dual B W →ₗ[B] (W → Ω) :=
    { toFun := fun f z => (f z : Ω)
      map_add' := fun f g => by ext z; simp
      map_smul' := fun c f => by ext z; simp [Subalgebra.smul_def] }
  refine coef_mem ι (fun f g e => LinearMap.ext fun z => Subtype.ext (congrFun e z)) b T n x ?_ a
  ext z
  simp [ι, x, hψ, hφ]

end Loc

theorem tri {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} (w f g : Fin n → V) (df dg : Fin n → Ω)
    (hg0 : ∀ a, dg a ≠ 0)
    (hf : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = df a ∧ f a = ∑ a', cf a' • w a')
    (hg : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = dg a ∧ g a = ∑ a', cf a' • w a') :
    ∃ T : Matrix (Fin n) (Fin n) Ω, (∀ a' a, a < a' → T a' a = 0) ∧ (∀ a, T a a = df a / dg a) ∧
      ∀ a, f a = ∑ a', T a' a • g a' := by
  choose cf f1 f2 f3 using hf
  choose cg g1 g2 g3 using hg
  let F : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cf a a'
  let G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cg a a'
  have hF : F.BlockTriangular id := fun a' a h => f1 a a' h
  have hG : G.BlockTriangular id := fun a' a h => g1 a a' h
  have hdet : IsUnit G.det := by
    rw [Matrix.det_of_upperTriangular hG, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    simpa [G, g2] using hg0 a
  haveI := G.invertibleOfIsUnitDet hdet
  have hT : (G⁻¹ * F).BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hG).mul hF
  have e : G * (G⁻¹ * F) = F := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  refine ⟨G⁻¹ * F, fun a' a h => hT h, fun a => ?_, fun a => ?_⟩
  · have := congrFun (congrFun e a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at this
    · rw [eq_div_iff (hg0 a), ← g2, ← f2, mul_comm]
      exact this
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hG h, zero_mul]
      · rw [hT h, mul_zero]
    · simp
  · simp only [g3, Finset.smul_sum, smul_smul]
    rw [f3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun e l) a
    rw [Matrix.mul_apply] at this
    refine Eq.trans ?_ (this.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _))
    rfl

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem omHT_fg (σ : E →+* K) : (D.omHT σ).FG :=
  by apply _root_.UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg <;> assumption

end

end PositivityTheory.HtPt.Ge
end

section

noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : ℕ}

theorem dual_exists (y : Fin N → M) (t : A) (G H Z : Matrix (Fin N) (Fin N) A)
    (h : H * G = 1 + t • Z) :
    ∃ i : Module.Dual A M →ₗ[A] (Fin N → A), ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z := by
  let ev : Module.Dual A M →ₗ[A] (Fin N → A) := LinearMap.pi fun j => Module.Dual.eval A M (y j)
  refine ⟨(Matrix.vecMulLinear H).comp ev, fun w j => ⟨Matrix.vecMul (ev w) Z j, ?_⟩⟩
  change Matrix.vecMul (Matrix.vecMul (ev w) H) G j = _
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul]
  rfl

theorem dual_unique (t : A) (G H Z : Matrix (Fin N) (Fin N) A) (h : G * H = 1 + t • Z)
    (a a' r : Fin N → A) (ha : ∀ j, ∃ z, ∑ l, a l * G l j = r j + t * z)
    (ha' : ∀ j, ∃ z, ∑ l, a' l * G l j = r j + t * z) : ∃ x : Fin N → A, a = a' + t • x := by
  choose z hz using ha
  choose z' hz' using ha'
  have h1 : Matrix.vecMul (a - a') G = t • (z - z') := by
    ext j
    rw [Matrix.sub_vecMul]
    change ∑ l, a l * G l j - ∑ l, a' l * G l j = t * (z j - z' j)
    rw [hz, hz']
    ring
  have h2 := congrArg (fun v => Matrix.vecMul v H) h1
  simp only [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
    Matrix.smul_vecMul] at h2
  refine ⟨Matrix.vecMul (z - z') H - Matrix.vecMul (a - a') Z, ?_⟩
  rw [smul_sub, ← h2]
  abel

theorem dual_split [Module.Projective A M] (y : Fin N → M) (t : A) (G : Matrix (Fin N) (Fin N) A)
    (hs : ∀ x : M, ∃ a : Fin N → A, ∃ x' : M, x = ∑ j, a j • y j + t • x')
    (i : Module.Dual A M →ₗ[A] (Fin N → A))
    (hi : ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z) :
    ∃ r : (Fin N → A) →ₗ[A] Module.Dual A M, ∀ w, ∃ w', r (i w) = w + t • w' := by
  let f : ((Fin N → A) × M) →ₗ[A] M :=
    (Fintype.linearCombination A y).coprod (t • LinearMap.id)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, x', e⟩ := hs x
    exact ⟨(a, x'), by rw [e]; simp [f, Fintype.linearCombination_apply]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let s₁ := (LinearMap.fst A _ _).comp s
  let s₂ := (LinearMap.snd A _ _).comp s
  have hs' : ∀ x, ∑ j, s₁ x j • y j + t • s₂ x = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [f, s₁, s₂, Fintype.linearCombination_apply] using this
  let B : (Fin N → A) →ₗ[A] Module.Dual A M := (dotProductBilin A A).compl₂ s₁
  refine ⟨B.comp (Matrix.vecMulLinear G), fun w => ?_⟩
  choose z hz using hi w
  refine ⟨B z - w.comp s₂, ?_⟩
  ext x
  change ∑ j, (∑ l, i w l * G l j) * s₁ x j = w x + t * (∑ j, z j * s₁ x j - w (s₂ x))
  conv_rhs => rw [← hs' x]
  rw [hs' x]
  nth_rewrite 2 [← hs' x]

  simp only [hz, map_add (f := _), map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_sub,
  Finset.mul_sum, mul_assoc]
  simp only [mul_comm (w _)]
  ring

end

theorem dual_map : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d m hσ hd hκ hom hproj
  obtain ⟨G, H, Z, Z', hG, hGH, hHG⟩ := gram_unit A K hAK E c hc p R N Ω D σ d (hσ σ) hd
  obtain ⟨-, -, hsurj⟩ := q_surj A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hσ _) hκ hom
  obtain ⟨t, ht⟩ := hκ
  have hR : ∀ Y : Matrix (Fin N) (Fin N) A, ((p : A) ^ R) • Y = ((p : A) ^ m) • (κ * t) • Y := by
    intro Y
    rw [ht, smul_smul]
    congr 1
    ring
  rw [hR] at hGH hHG
  let y : Fin N → D.omHT (σ.comp c.toRingHom) := fun j =>
    ⟨_, proj_mem_omHT D (σ.comp c.toRingHom) (h_mem_om' D (Pi.single j 1))⟩
  have key : ∀ i, D.IsDualMap σ d m i ↔
      ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + (p : A) ^ m * z := by
    intro i
    constructor
    · intro h w j
      obtain ⟨z, hz⟩ := h w j (y j) rfl
      refine ⟨z, hAK ?_⟩

      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
    · intro h w j y' hy'
      obtain rfl : y' = y j := Subtype.ext hy'
      obtain ⟨z, hz⟩ := h w j
      refine ⟨z, ?_⟩

      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
  simp only [key]
  refine ⟨dual_exists y _ G H _ hHG, fun i i' hi hi' w =>
    dual_unique _ G H _ hGH _ _ (fun j => w (y j)) (hi w) (hi' w), fun i hi =>
    dual_split y _ G (fun x => ?_) i hi⟩
  obtain ⟨a, x', hx', e⟩ := hsurj x x.2
  refine ⟨a, ⟨x', hx'⟩, Subtype.ext ?_⟩
  rw [e, Submodule.coe_add, Submodule.coe_sum]
  rfl

end PositivityTheory.HtPt.Ga
end
end
