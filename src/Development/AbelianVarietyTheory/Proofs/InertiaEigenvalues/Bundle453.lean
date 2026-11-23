module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle430
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle424
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle399
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandard
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelSenWeightCount
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle442
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix Topology Filter

namespace GlobalTheory.LocGL.ProRadOnto

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_mk_eq {π : Representation ℂ G V} (hπ : IsAdmissible π) {I N : Subgroup G}
    (ho : IsOpen (I : Set G)) (hc : IsCompact (I : Set G)) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M) (hM₀ : ∀ d ∈ M₀, s d ∈ I)
    (C : Set G) (hfac : ∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c)
    (hcon : ∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, d * t = t * d) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U)
    (y : Jacquet π N) (hy : y ∈ fixed (jacquet π N s hs) M₀) :
    ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  set p := (twKer π N 1).mkQ with hp
  set σ := jacquet π N s hs with hσ
  have hps : ∀ m v, p (π (s m) v) = σ m (p v) := fun _ _ => rfl
  have hpN : ∀ x ∈ N, ∀ v, p (π x v) = p v := fun x hx v =>
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨x, hx⟩, v, by simp⟩)
  obtain ⟨u, rfl⟩ : ∃ u, p u = y := Submodule.mkQ_surjective _ y
  obtain ⟨t, htc, ht⟩ := hcon _ ((ho.inter (hπ.1 u)).mem_nhds ⟨one_mem I, by simp⟩)
  set Y := (fixed π I).map p with hY
  haveI := hπ.2 I ho hc
  have key : ∀ w, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) w = w) → (∀ d ∈ M₀, σ d (p w) = p w) →
      σ t (p w) ∈ Y := by
    intro w h1 h2
    refine IwahoriOnto.exists_fixed_map_eq hπ.1 hc p (π (s t) w) fun g hg => ?_
    obtain ⟨d, hd, x, hx, c, hcC, rfl⟩ := hfac g hg
    have h3 : π c (π (s t) w) = π (s t) w := by
      conv_rhs => rw [← h1 c hcC]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3, hps, hpN x hx, hps,
      ← Module.End.mul_apply, ← map_mul, htc d hd, map_mul, Module.End.mul_apply, h2 d hd]
  have hinj : Function.Injective (σ t) := by
    intro a b hab
    have := congrArg (σ t⁻¹) hab
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hst : ∀ z ∈ Y, σ t z ∈ Y := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ g ∈ I, π g w = w := fun g hg => by simpa using hw ⟨g, hg⟩
    exact key w (fun c hcC => hw' _ (ht c hcC).1) fun d hd => by rw [← hps, hw' _ (hM₀ d hd)]
  have hsurj : Function.Surjective ((σ t).restrict hst) :=
    LinearMap.surjective_of_injective fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  obtain ⟨z, hz⟩ := hsurj ⟨_, key u (fun c hcC => (ht c hcC).2) fun d hd => by simpa using hy ⟨d, hd⟩⟩
  have : (z : Jacquet π N) = p u := hinj (congrArg Subtype.val hz)
  exact this ▸ z.2

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem jMinus_contract (e : (Σ a, m a) ≃ n) : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : Levi k m,
    (∀ d : Levi k m, d * t = t * d) ∧ ∀ c ∈ jMinus k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro U hU
  let r : α → ℕ := fun a => (Finset.univ.filter fun b => b < a).card
  have hr : ∀ a b, b < a → r b < r a := fun a b hab =>
    Finset.card_lt_card ⟨fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.trans hab, fun hs => by simpa using hs (show b ∈ _ by simpa using hab)⟩
  let S : kˣ → Levi k m := fun x a => Units.map (Matrix.scalar (m a)).toMonoidHom (x ^ r a)⁻¹
  let T : kˣ → n → kˣ := fun x i => (x ^ r (blk e i))⁻¹
  have hST : ∀ x, leviEmb k e (S x) = diagT k n (T x) := by
    intro x
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    rw [val_diagT, diagonal_apply]
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      simp [S, T, Matrix.scalar_apply, diagonal_pow, diagonal_apply, inv_pow]
    · rw [leviEmb_apply_ne k e _ h, if_neg fun h' => h (congrArg Sigma.fst (e.injective h'))]
  have hcomm : ∀ x (d : Levi k m), d * S x = S x * d := fun x d => funext fun a => Units.ext
    ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq).symm
  let F : Filter (kˣ × jMinus k e) := (comap (fun x : kˣ => (x : k)) (𝓝 0)) ×ˢ ⊤
  have hent : ∀ (x : kˣ) (c : GL n k) i j, ((diagT k n (T x))⁻¹ * c * diagT k n (T x)).val i j =
      (x : k) ^ r (blk e i) * c.val i j * ((x : k) ^ r (blk e j))⁻¹ := by
    intro x c i j
    rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]
    simp [T]
  have hT : Tendsto (fun p : kˣ × jMinus k e => (diagT k n (T p.1))⁻¹ * p.2.1 * diagT k n (T p.1)) F
      (𝓝 1) := by
    rw [SplitFlip.isEmbedding_val_GL.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_def, hent]
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply, Units.val_one]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h0 : ∀ p : kˣ × jMinus k e, (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := fun p =>
        (mem_parabLower_iff k).1 ((mem_unipRadLower k).1 p.2.2.1).1 a b i j hab
      simp only [h0, mul_zero, zero_mul, IwahoriFactor.one_ne e hab.ne]
      exact tendsto_const_nhds
    · have h1 : ∀ p : kˣ × jMinus k e, (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) *
          ((p.1 : k) ^ r a)⁻¹ = (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) := fun p => by
        rw [((mem_unipRadLower k).1 p.2.2.1).2 a i j, IwahoriFactor.one_same, mul_comm, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ p.1.ne_zero), one_mul]
      simp only [h1]
      exact tendsto_const_nhds
    · rw [IwahoriFactor.one_ne e hab.ne', (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
      intro γ _
      have h1 : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ h => h⟩
      have h2 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ h => h⟩
      filter_upwards [prod_mem_prod (preimage_mem_comap (inter_mem h1 h2)) univ_mem] with p hp
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt (hr a b hab)
      have hint : valuation k ((p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) ≤ 1 := by
        have := StepData.mem_KOne.1 p.2.2.2 (e ⟨a, i⟩) (e ⟨b, j⟩)
        rw [Matrix.sub_apply, IwahoriFactor.one_ne e hab.ne', sub_zero] at this
        exact this.le
      have : (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) * ((p.1 : k) ^ r b)⁻¹ =
          p.1 * (p.1 ^ l * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) := by
        rw [hl]; field_simp; ring
      show valuation k _ < _
      rw [this, map_mul, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (mul_le_one' (pow_le_one' hp.1.2.le _) hint)).trans_lt hp.1.1
  haveI : (comap (fun x : kˣ => (x : k)) (𝓝 0)).NeBot := by
    refine comap_neBot fun s hs => ?_
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ValueGroupWithZero k, δ ≠ 0 ∧ δ < γ :=
      ⟨uniformizer k * γ, by simp, mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one⟩
    obtain ⟨x, rfl⟩ := valuation_surjective δ
    exact ⟨Units.mk0 x (by simpa using hδ0), hγ hδ⟩
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (mem_prod_top.1 (hT hU))
  exact ⟨S x, hcomm x, fun c hc => by rw [hST]; exact hx ⟨c, hc⟩⟩

end Local

end GlobalTheory.LocGL.ProRadOnto


open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel in
theorem GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π → ∀ y : Jacquet π (unipRad k e), y ∈ fixed (jacU e π) (leviKOne k m) → ∃ v ∈ fixed π (proRad k e), (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = y := by
  intro k _ _ _ _ α n _ _ m _ _ _ _ e V _ _ π hπ y hy
  obtain ⟨v, hv, h⟩ := ProRadOnto.exists_fixed_mk_eq hπ (isOpen_levelPre _) (isCompact_levelPre _) (leviEmb k e)
    (N := unipRad k e) (leviEmb_mem_normalizer k e) (leviKOne k m)
    (fun d hd => jLevi_le_proRad e ⟨d, hd, rfl⟩) (jMinus k e) (fun g hg => by
      obtain ⟨d, ⟨d', hd', hd⟩, u, hu, c, hc, h⟩ := IwahoriFactor.levi_plus_minus e hg
      exact ⟨d', hd', u, hu.1, c, hc, h.trans (by rw [hd])⟩)
    (fun U hU => by
      obtain ⟨t, ht, h⟩ := ProRadOnto.jMinus_contract e U hU
      exact ⟨t, fun d _ => ht d, h⟩) y hy
  exact ⟨v, hv, h⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.EpsInertia

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem mem_GK (σ : GQ l) (h : ∀ x : E, σ (Bw.j (algebraMap E Ω x)) = Bw.j (algebraMap E Ω x)) :
    σ ∈ GK Bw.Kw := by
  have hc : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun x => (spectralNorm_eq_of_equiv σ x).symm).continuous
  rintro ⟨x, hx⟩
  have hcl : closure (Set.range fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {y | σ y = y} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact h y) (isClosed_eq hc continuous_id)
  exact hcl (Bw.j_dense hx)

theorem cycZ_bridge [IsAlgClosed Ω] (g : ↥Gw) :
    cycZ E Ω l (g : Ω ≃ₐ[E] Ω) = cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) := by
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := Bw.j.charZero
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.1 fun m => ?_)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
  have hζ' := hζ.map_of_injective Bw.j.injective
  have ha : (g : Ω ≃ₐ[E] Ω) ζ =
      ζ ^ (((cycZ E Ω l (g : Ω ≃ₐ[E] Ω) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[E] Ω) Ω (g : Ω ≃ₐ[E] Ω)) ζ hζ.pow_eq_one
  have hb : ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) (Bw.j ζ) = Bw.j ζ ^
      (((cycZ ℚ_[l] (Om l) l ((Bw.e g : ↥(GK Bw.Kw)) : GQ l) : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut (GQ l) (Om l) ((Bw.e g : ↥(GK Bw.Kw)) : GQ l)) _ hζ'.pow_eq_one
  rw [Bw.e_comm, ha, map_pow] at hb
  exact ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)

end Bridge

theorem fix_roots {l : ℕ} [Fact l.Prime] (σ : GQ l) (s : ℕ) (z : ℤ_[l])
    (h : ((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ s * z) (y : Om l)
    (hy : y ^ l ^ s = 1) : σ y = y := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hb : σ y = y ^ (((cycZ ℚ_[l] (Om l) l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow s).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) _ hy
  have h0 : ((l : ZMod (l ^ s))) ^ s = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h, map_add (f := _), map_one, map_mul, map_pow, map_natCast, h0, zero_mul, add_zero, ZMod.val_one_eq_one_mod] at hb
  rw [hb, ← pow_eq_pow_mod 1 hy, pow_one]

theorem epsAll : ∀ (D : D7) (i : D.nd.Loc), EpsAll D i := by
  intro D i w hw z
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hs : D.nd.s0 i ≠ 0 := by
    have := UpperTheory.KStar.S0.one_le_localLevel D.nd i
    omega
  have hu : IsUnit (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * z) := by
    rw [← sub_neg_eq_add]
    refine IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h => ?_
    have h1 := (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h))
    exact PadicInt.irreducible_p.not_isUnit h1
  obtain ⟨u, hu⟩ := hu
  obtain ⟨σ, hσK, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ GK (D.nbr i w hw).Kw := by
    refine mem_GK _ σ fun x => ?_
    have hle : MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i]
        {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      have hm : ∀ y, σ y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := fun y hy => by
        rintro ⟨_, k, rfl⟩
        exact (MulAction.stabilizer (GQ (D.nd.l i)) y).zpow_mem hy k
      refine sup_le (fun y hy => hm y (hσK y hy)) (IntermediateField.adjoin_le_iff.2 fun y hy => hm y ?_)
      exact fix_roots σ _ z (by rw [hσu, hu]) y hy
    exact hle (GlobalTheory.T.hostField_image_mem_unramified_adjoin_rootsOfUnity D i w hw x) ⟨σ, Subgroup.mem_zpowers σ⟩
  set g := (D.nbr i w hw).e.symm ⟨σ, hσ⟩ with hg
  have he : (((D.nbr i w hw).e g : ↥(GK (D.nbr i w hw).Kw)) : GQ (D.nd.l i)) = σ := by
    rw [hg, MulEquiv.apply_symm_apply]
  refine ⟨g.1, ⟨g.2, fun x hx => ?_⟩, by rw [cycZ_bridge (D.nbr i w hw) g, he, hσu, hu]⟩
  have h1 := GlobalTheory.UnramInertia.norm_sub_lt_one_of_fix _ σ hσK _
    ((D.nbr_ind i w hw x).1 (((D.nd.plOm.1 w).valuation_le_one_iff x).1 hx))
  rw [← he, (D.nbr i w hw).e_comm, ← map_sub] at h1
  set y := g.1 x - x
  by_cases hy : y = 0
  · rw [hy, map_zero]; exact zero_lt_one
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hy))] at h
  rw [← not_le, h, not_le]
  exact h1

end GlobalTheory.EpsInertia

end
end

section

noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  let e' := stdBlocks (fun _ : Fin 1 => z.1) hd
  obtain ⟨φ⟩ : Nonempty ((multiProd e fun _ => z.rep).Equiv (multiProd e' fun _ => z.rep)) := by
    obtain ⟨w, hw⟩ := Placing.exists_moves (R := k) e' e
    have hw' : Placing.Moves e e' w⁻¹ := by
      intro g x y
      rw [← hw (w⁻¹ * g * w⁻¹⁻¹) x y]
      simp [mul_assoc]
    let ρ := twist (piTensor fun _ : Fin 1 => z.rep) (deltaHalf k fun _ : Fin 1 => Fin z.1)
    have conjugate {f f' : (Σ _ : Fin 1, Fin z.1) ≃ Fin z.1} {v : GL (Fin z.1) k}
        (hv : Placing.Moves f f' v) (p : parab k f) :
        ∃ q : parab k f', (q : GL (Fin z.1) k) = v * p * v⁻¹ ∧
          (ρ.comp (leviProj k f')) q = (ρ.comp (leviProj k f)) p := by
      have hq : v * (p : GL (Fin z.1) k) * v⁻¹ ∈ parab k f' := by
        rw [mem_parab]
        intro i j hij
        exact (hij.ne (Subsingleton.elim _ _)).elim
      refine ⟨⟨_, hq⟩, rfl, ?_⟩
      simp only [MonoidHom.comp_apply]
      congr 1
      refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
      simpa only [leviProj_apply] using hv (p : GL (Fin z.1) k) ⟨a, i⟩ ⟨a, j⟩
    exact Placing.smInd_equiv w (conjugate hw) (conjugate hw')
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

namespace GlobalTheory.Pass.LocDual

theorem T2 {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {S S' : Submodule O M} (H : Submodule O M)
    (h : S ≤ S') : BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  unfold BlochKatoDuality.lenMod
  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right h H
  let f : ↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype →ₗ[O] ↥(S' ⊔ H) ⧸ H.comap (S' ⊔ H).subtype :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (fun x hx => hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have := (Submodule.Quotient.mk_eq_zero _).1 hz
  exact this



theorem main : StepLocDual := by
  intro D hLOC hBK hFont hPot i r hr Xs w hw hdeg n e hPF hLF k M hSub
  unfold LocBoundP
  apply GlobalTheory.T.lengthModulo_span_le_of_forall_finset
  intro F hF
  obtain ⟨X, hX, hle⟩ := GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice D hFont i r hr Xs w hw n hPF k M hSub F hF
  obtain ⟨hdrX, X', PX, hdX, hsX⟩ := GlobalTheory.T.potential_family_summand_restriction D hFont hPot i r hr Xs w hw n hPF X hX
  obtain ⟨hdrU, U', PU, hsU, LT', hdU, hrk⟩ := GlobalTheory.T.crystalline_potential_family D hFont hPot hBK i r hr Xs w hw hdeg n hPF k M hSub
  have hLift := GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily (Br.PD D.loc D.nbr i w hw) _ e X' U' hLF hsX hsU
  have hTw : IsTwistRep (1 : Br.G D.nbr i w hw →* (Br.LL D.nbr i w hw)ˣ)⁻¹ X.ρ X.ρ :=
    ⟨LinearEquiv.refl _ _, fun g x => by simp⟩
  have hHyp : BlochKatoDuality.Hyp (Br.PD D.loc D.nbr i w hw) X X (locU i w hw M hSub.1) X' U' 1 PX PU
      (Br.locLat D.nbr i w hw M) LT' e := ⟨hTw, hdrU, hdX, hdU, Or.inr ⟨hdrX, hLift⟩⟩
  obtain ⟨m, kk, hm, hk, hmk⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL) X X (locU i w hw M hSub.1) X' U' 1 PX PU
    (Br.locLat D.nbr i w hw M) LT' e hHyp
  refine (T2 _ hle).trans ?_
  change BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤ _
  have hm' : BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) = m := hm
  have hk' : lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = kk := hk
  rw [hm', hk']
  have : m ≤ 2 * k * e * kk :=
    hmk.trans ((Nat.mul_le_mul_right kk (Nat.mul_le_mul_left e hrk)).trans_eq (by ring))
  exact_mod_cast this

end GlobalTheory.Pass.LocDual
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.twistedPhiGammaModel_character_eq_standard : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  first | exact @GlobalTheory.Models.CharModel.model_chr_eq | exact GlobalTheory.Models.CharModel.model_chr_eq | (intros; apply GlobalTheory.Models.CharModel.model_chr_eq <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.twistedPhiGammaModel_sen_weight_count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  first | exact @GlobalTheory.ModelCount.count | exact GlobalTheory.ModelCount.count | (intros; apply GlobalTheory.ModelCount.count <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_smallSubgroup_cocycleForm_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  first | exact @GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero | exact GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero | (intros; apply GlobalTheory.NewPrime.FormNonzero.exists_bform_ne_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.cauchy_identity_schur_formal_degree : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  exact @GlobalTheory.JSW.CauchyGlue.cauchy_formal
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  first | exact @GlobalTheory.ExpImage.nearZ_of_forall_Lat | exact GlobalTheory.ExpImage.nearZ_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.nearZ_of_forall_Lat <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) * ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.epsT_pow_taylor | exact GlobalTheory.ExpImage.epsT_pow_taylor | (intros; apply GlobalTheory.ExpImage.epsT_pow_taylor <;> assumption)
end
