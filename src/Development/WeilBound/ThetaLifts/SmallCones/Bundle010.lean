module

public import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.ThetaLifts.SmallCones.SliceAd

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKCT.So

open PositivityTheory.ThKOwn.KPol
open scoped SchwartzMap LineDeriv

section Fil

variable {S ι : Type} [AddCommGroup S] [Module ℂ S]

def fil (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : ℕ → Submodule ℂ S
  | 0 => P
  | m + 1 => fil P D m ⊔ ⨆ i, (fil P D m).map (D i)

theorem fil_fin [Finite ι] (P : Submodule ℂ S) [FiniteDimensional ℂ P] (D : ι → S →ₗ[ℂ] S) (m : ℕ) :
    FiniteDimensional ℂ (fil P D m) := by
  induction m with
  | zero => exact (inferInstance : FiniteDimensional ℂ P)
  | succ m ih => exact (inferInstance : FiniteDimensional ℂ ↥(fil P D m ⊔ ⨆ i, (fil P D m).map (D i)))

theorem fil_mono (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : Monotone (fil P D) := monotone_nat_of_le_succ fun _ => le_sup_left

theorem fil_step (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) {m : ℕ} {f g : S} (hf : f ∈ fil P D m)
    (hg : g ∈ Submodule.span ℂ (Set.range fun i => D i f)) : g ∈ fil P D (m + 1) := by
  refine (Submodule.span_le.2 ?_ : _ ≤ fil P D (m + 1)) hg
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩)

theorem fil_stab (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) (A : S →ₗ[ℂ] S) (h0 : ∀ f ∈ P, A f ∈ P)
    (h : ∀ i f, A (D i f) ∈ Submodule.span ℂ (Set.range fun j => D j (A f))) (m : ℕ) : fil P D m ≤ (fil P D m).comap A := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    refine sup_le (fun f hf => Submodule.mem_sup_left (ih hf)) (iSup_le fun i => ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact fil_step P D (ih hf) (h i f)

end Fil

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (lam : V →ₗ[ℝ] V →L[ℝ] ℝ)

def dopL (w : V × V) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop w.1 (lam w.2)
  map_add' f g := by
    ext x
    have : fderiv ℝ (f + g : 𝓢(V, ℂ)) x = fderiv ℝ f x + fderiv ℝ g x := ((f.hasFDerivAt x).add (g.hasFDerivAt x)).fderiv
    simp only [SchwartzMap.add_apply, dop_apply, this, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    have : fderiv ℝ (c • f : 𝓢(V, ℂ)) x = c • fderiv ℝ f x := ((f.hasFDerivAt x).const_smul c).fderiv
    simp only [SchwartzMap.smul_apply, dop_apply, this, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem dopL_apply (w : V × V) (f : 𝓢(V, ℂ)) : dopL lam w f = dop w.1 (lam w.2) f := rfl

def evD (f : 𝓢(V, ℂ)) (x : V) : V × V →ₗ[ℝ] ℂ where
  toFun w := dopL lam w f x
  map_add' a b := by
    simp only [dopL_apply, Prod.fst_add, Prod.snd_add, map_add (f := _), dop_add, SchwartzMap.add_apply]
  map_smul' c a := by
    simp only [dopL_apply, dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Complex.real_smul]
    push_cast
    ring

theorem dopL_mem {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (V × V)) (w : V × V) (f : 𝓢(V, ℂ)) :
    dopL lam w f ∈ Submodule.span ℂ (Set.range fun i => dopL lam (b i) f) := by
  have : dopL lam w f = ∑ i, (b.repr w i : ℂ) • dopL lam (b i) f := by
    ext x
    have h := congrArg (evD lam f x) (b.sum_repr w).symm

    rw [map_sum] at h
    rw [SchwartzMap.sum_apply]
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def vacs (S : Set ((V × V) × V × V)) : Submodule ℂ 𝓢(V, ℂ) :=
  ⨅ γ ∈ S, LinearMap.ker (dopL lam γ.2 - Complex.I • dopL lam γ.1)

theorem mem_vacs {S : Set ((V × V) × V × V)} {f : 𝓢(V, ℂ)} :
    f ∈ vacs lam S ↔ ∀ γ ∈ S, dopL lam γ.2 f = Complex.I • dopL lam γ.1 f := by
  simp only [vacs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]

theorem ray_zero (f : 𝓢(V, ℂ)) (x : V) (c : ℂ) (h : ∀ t : ℝ, fderiv ℝ f (t • x) x = t * c * f (t • x)) (h0 : f 0 = 0) : f x = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) ^ 2 * c / 2))) 0 t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) x) t :=
      (f.hasFDerivAt (t • x)).comp_hasDerivAt t (by simpa using (hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2 * c / 2)) (-(t * c)) t := by
      have := ((((hasDerivAt_id t).ofReal_comp).fun_pow 2).mul_const c).div_const 2 |>.fun_neg
      refine this.congr_deriv ?_
      simp
      ring
    refine (h1.fun_mul h2.cexp).congr_deriv ?_
    rw [h]
    ring
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [h0] using this

theorem vacs_fin [FiniteDimensional ℝ V] (hl : Function.Injective lam) (S : Set ((V × V) × V × V)) (hS : ∀ p, ∃ γ ∈ S, γ.1 = p) :
    FiniteDimensional ℂ (vacs lam S) := by
  let Γ := Submodule.span ℝ S
  have hΓ : ∀ f ∈ vacs lam S, ∀ x, ∀ γ ∈ Γ, evD lam f x γ.2 = Complex.I * evD lam f x γ.1 := fun f hf x γ hγ => by
    induction hγ using Submodule.span_induction with
    | mem γ h => exact DFunLike.congr_fun ((mem_vacs lam).1 hf γ h) x
    | zero => simp
    | add a b _ _ ha hb => rw [Prod.fst_add, Prod.snd_add, map_add (f := _), map_add (f := _), ha, hb, mul_add]
    | smul c a _ ha => rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, ha, mul_smul_comm]
  have key : ∀ f ∈ vacs lam S, f 0 = 0 → f = 0 := fun f hf h0 => by
    let π : Γ →ₗ[ℝ] V × V := ((LinearMap.fst ℝ V V).prodMap (LinearMap.fst ℝ V V)) ∘ₗ Γ.subtype
    by_cases hπ : Function.Injective π
    · have h1 := LinearMap.finrank_le_finrank_of_injective hπ
      have h2 := LinearMap.finrank_le_finrank_of_surjective (f := LinearMap.fst ℝ (V × V) (V × V) ∘ₗ Γ.subtype) fun p => by
        obtain ⟨γ, h, e⟩ := hS p
        exact ⟨⟨γ, Submodule.subset_span h⟩, e⟩
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).1 hπ
      ext x
      obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e⟩ := hs (0, x)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = x := Prod.ext_iff.1 e
      refine ray_zero f a' (2 * Real.pi * Complex.I * (lam b' a' - Complex.I * lam b a')) (fun t => ?_) h0
      have := hΓ f hf (t • a') _ hγ
      simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero, map_smul, smul_eq_mul] at this
      push_cast at this
      linear_combination this
    · obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e, hne⟩ := (Submodule.ne_bot_iff _).1 fun h => hπ (LinearMap.ker_eq_bot.1 h)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = 0 := Prod.ext_iff.1 e
      have hz : ∀ x, f x ≠ 0 → lam b x = 0 ∧ lam b' x = 0 := fun x hx => by
        have := hΓ f hf x _ hγ
        simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero] at this
        have h3 : (2 * Real.pi * Complex.I) * f x * (lam b' x - Complex.I * lam b x) = 0 := by linear_combination -this
        have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero (by simp [Real.pi_ne_zero]) hx)
        have h5 := congrArg Complex.re h4
        have h6 := congrArg Complex.im h4
        simp at h5 h6
        exact ⟨h6, h5⟩
      by_contra hf0
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hf0 (SchwartzMap.ext hc)
      have hk : ∀ c, (∀ x, f x ≠ 0 → lam c x = 0) → c = 0 := fun c hc => by
        have ht : LinearMap.ker (lam c).toLinearMap = ⊤ := Submodule.eq_top_of_nonempty_interior' _
          ⟨x, mem_interior.2 ⟨{y | f y ≠ 0}, hc, isOpen_ne_fun f.continuous continuous_const, hx⟩⟩
        refine hl ?_
        rw [map_zero]
        ext y
        exact (ht ▸ Submodule.mem_top : y ∈ LinearMap.ker (lam c).toLinearMap)
      obtain rfl := hk b fun x hx => (hz x hx).1
      obtain rfl := hk b' fun x hx => (hz x hx).2
      exact hne rfl
  let ev : vacs lam S →ₗ[ℂ] ℂ := { toFun := fun f => f.1 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun f h => Subtype.ext (key f.1 f.2 h))

theorem level_fin {X Y Z S : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup S] [Module ℂ S]
    (pt : X → Y → Z) (hpt : ∀ z, ∃ x y, z = pt x y) (c : S →ₗ[ℂ] (X → ℂ)) (P : Submodule ℂ S) [FiniteDimensional ℂ P] {C U : Set Y}
    (hC : IsCompact C) (hU : U ∈ nhds 0) (N : Submodule ℂ (Z → ℂ)) (h1 : ∀ Ψ ∈ N, ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = c f x)
    (h2 : ∀ Ψ ∈ N, ∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) (h3 : ∀ Ψ ∈ N, ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)) :
    FiniteDimensional ℂ N := by
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover (fun y => {y' | y' - y ∈ U}) fun y _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  let ev : N →ₗ[ℂ] (s → P.map c) :=
    { toFun := fun Ψ y => ⟨fun x => Ψ.1 (pt x y), by
        obtain ⟨f, hf, e⟩ := h1 _ Ψ.2 y
        exact ⟨f, hf, funext fun x => (e x).symm⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun Ψ h => Subtype.ext (funext fun z => ?_))
  obtain ⟨x, y, rfl⟩ := hpt z
  by_cases hy : y ∈ C
  · obtain ⟨y₀, h₀, hy₀⟩ := Set.mem_iUnion₂.1 (hs hy)
    have := h3 _ Ψ.2 x y₀ _ hy₀
    rw [add_sub_cancel] at this
    rw [this]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨y₀, h₀⟩)) x
  · exact h2 _ Ψ.2 x y hy

end PositivityTheory.ThKCT.So

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT.Line

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Ad PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}

theorem cA_cA (h : IsCMExt F E σ) (a : AE F E) : cA σ (cA σ a) = a := by
  obtain ⟨t⟩ : Nonempty (E →+* ℂ) := inferInstance
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[F] σ (σ x) = _
    rw [t.injective (show t (σ (σ x)) = t x by rw [h.2.2.2, h.2.2.2]; exact Complex.conj_conj _)]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem hTens_inc (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F x) (incM F y) = inclR (F := F) (AF F) (hTens σ J J' x y) := by

  simp only [hTens, incM, Matrix.map_apply, map_sum, map_mul]
  rfl

theorem hTens_smul (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) (a b : E) :
    hTens σ J J' (a • x) (b • y) = a * σ b * hTens σ J J' x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem incM_smul (a : E) (x : Matrix (Fin n) (Fin d) E) : incM F (a • x) = inclR (F := F) (AF F) a • incM F x := by
  ext i j
  exact map_mul (inclR (F := F) (AF F)) _ _

theorem exists_dual (B : Base F E) {X : Spc F E n} {W : Spc F E d} {I : Set (Ten F E n d)} {v₀ z₀ : Matrix (Fin n) (Fin d) E}
    (hI : ∀ a : AE F E, a • incM F z₀ ∈ I) (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀)))
    {m : ℕ} (b : Module.Basis (Fin m) F E) : ∃ z, Dual σ X W I (fun j => b j • v₀) z := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 : hTens σ X.J W.J z₀ v₀ ≠ 0 := fun h => by
    rw [hTens_inc, h, map_zero] at hu
    exact (hu.map (piInf (B.emb w))).ne_zero (map_zero _)
  refine ⟨fun i => (-σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀) • z₀, fun j a => ?_, fun i j => ?_⟩
  · rw [incM_smul, ← smul_assoc]
    exact hI _
  · rw [sy, symp, hTens_inc, hTens_smul, show -σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀ * σ (b j) * hTens σ X.J W.J z₀ v₀ =
      -σ (b j * b.traceDual i) by rw [map_mul]; field_simp, map_neg, neg_one_mul, neg_neg]
    change Algebra.trace (AF F) _ ((1 : AF F) ⊗ₜ[F] _) = _
    rw [GlobalTheory.ThK.Dbl.Dense.trace_tmul, one_mul, show σ (b j * b.traceDual i) =
      AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ) (b j * b.traceDual i) from rfl,
      Algebra.trace_eq_of_algEquiv, Module.Basis.trace_mul_traceDual]
    simp only [eq_comm (a := i)]
    split_ifs <;> simp

theorem norm_piInf_smul (h : IsCMExt F E σ) {w : InfinitePlace F} (t : EmbOver E w) (y : AF F) (β : AE F E) :
    ‖piInf t (y • β)‖ = normAtPlace w (evI F y) * ‖piInf t β‖ := by
  haveI := h.1
  rw [Algebra.smul_def, map_mul, norm_mul, normAtPlace_apply_of_isReal (IsTotallyReal.isReal w)]
  congr 1
  change ‖infEmb t (evInf F w y ⊗ₜ[F] (1 : E))‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (y.1 w)‖
  rw [infEmb_tmul, map_one, mul_one, (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _)]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

def Nice {κ : Type} [Fintype κ] (μ : Measure (AE F E)ˣ) (z : ℕ) (v : AE F E → (κ → AF F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (φ : ι → (κ → Af F) → ℂ) (g : ι → AE F E → SInf F κ), (∀ i, φ i ∈ SB _) ∧ (∀ i, Continuous (g i)) ∧
    (∀ a, v a = ∑ i, pureA F (g i a) (φ i)) ∧
    ∀ q : Seminorm ℂ (SInf F κ), Continuous q → ∀ i, Integrable (fun l : (AE F E)ˣ => q (g i l) * (absE F E l : ℝ) ^ z) μ


theorem nice (hS : Slice) (hT : TateAbs) {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (he : IsEv B M M₁ ι ι' I e) {v₀ z₀ : Matrix (Fin n) (Fin d) E} (hI : ∀ a : AE F E, a • incM F z₀ ∈ I)
    (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀))) (τ : AE F E →ₐ[AF F] AE F E)
    (hτ : ∀ a, τ (τ a) = a) (μ : Measure (AE F E)ˣ) (hμ : μ.IsHaarMeasure) {z : ℕ} (hz : 2 ≤ z) {Ψ : Fn F n d}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) : Nice μ z fun a => e (M.co.rho B.ψ (τ a • incM F v₀) Ψ) := by
  induction hΨ using Submodule.span_induction with
  | zero =>
    letI : IsEmpty Empty := ⟨Empty.elim⟩
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun a => ?_, fun _ _ i => i.elim⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← map_zero e]
    exact congrArg e (funext fun x => mul_zero _)
  | add x y _ _ hx hy =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    obtain ⟨ι₂, _, φ', g', h1', h2', h3', h4'⟩ := hy
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim φ φ', Sum.elim g g', Sum.forall.2 ⟨h1, h1'⟩, Sum.forall.2 ⟨h2, h2'⟩, fun a => ?_,
      fun q hq => Sum.forall.2 ⟨h4 q hq, h4' q hq⟩⟩
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← h3 a, ← h3' a, ← map_add (f := _)]
    congr 1
    exact funext fun x => mul_add _ _ _
  | smul c x _ hx =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    refine ⟨ι₁, inferInstance, fun i => c • φ i, g, fun i => Submodule.smul_mem _ _ (h1 i), h2, fun a => ?_, h4⟩
    simp only [GlobalTheory.ThK.Dbl.Dense.pureA_smul]
    rw [← Finset.smul_sum, ← h3 a, ← map_smul]
    congr 1
    exact funext fun x => mul_left_comm _ _ _
  | mem x hx =>
    obtain ⟨f, φ, hφ, rfl⟩ := hx
    obtain ⟨⟨_, -⟩, -, _, -, -, _, -⟩ := ideleTop F E
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
    let b := Module.finBasis F E
    let Bt := Algebra.TensorProduct.basis (AF F) b
    obtain ⟨zz, hD⟩ := exists_dual B hI hu b
    obtain ⟨r, φ₁, C, A, h1, h2, h3, h4, h5, h6⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he _ _ _ hD φ hφ
    let y : AE F E → Fin (Module.finrank F E) → AF F := fun a => Bt.equivFun (τ a)
    have hy : Continuous y := IsModuleTopology.continuous_of_linearMap (Bt.equivFun.toLinearMap ∘ₗ τ.toLinearMap)
    have e1 : ∀ a, τ a = ∑ j, y a j • Bt j := fun a => (Bt.sum_equivFun _).symm
    have e2 : ∀ a, a = ∑ j, y a j • τ (Bt j) := fun a => by

      conv_lhs => rw [← hτ a, e1 a, map_sum]
      simp only [map_smul]
    refine ⟨Fin r, inferInstance, φ₁, fun i a => A i (y a) f, h1, fun i => (h3 i f).comp hy, fun a => ?_, fun q hq i => ?_⟩
    · beta_reduce
      rw [← h4, lin, e1 a, Finset.sum_smul]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [incM_smul, smul_assoc, Algebra.TensorProduct.basis_apply]
      rfl
    obtain ⟨N, hN⟩ := hT F E σ B hB μ hμ z hz
    obtain ⟨p, -, hp⟩ := h6 q N hq
    have hN' := hN _ (h2.image (f := fun c => ∑ j, mk 0 (c j) • τ (Bt j)) (continuous_finsetSum _ fun j _ =>
      Continuous.smul (f := fun c : _ → Af F => mk 0 (c j)) (g := fun _ => τ (Bt j))
        (continuous_const.prodMk (continuous_apply j)) continuous_const))
    set K := ∑ j, ∑ w, ‖piInf (B.emb w) (τ (Bt j))‖ with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine ⟨((hq.comp ((h3 i f).comp (hy.comp Units.continuous_val))).mul
      ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow z)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun l => ?_) ((lintegral_indicator_le _ _).trans_lt
      ((lintegral_const_mul' (ENNReal.ofReal (p f * (1 + K) ^ N)) _ ENNReal.ofReal_ne_top).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN')))
    by_cases hl : (fun j => (y l j).2) ∈ C
    · rw [Set.indicator_of_mem, ← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal (by positivity)]
      · refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_div_assoc, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [le_div_iff₀ (by positivity)]
        refine le_trans ?_ (mul_le_mul_of_nonneg_right (hp i (y l) f) (by positivity))
        rw [mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (apply_nonneg _ _)
        set s := ∑ j, ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)) with hs
        have hs1 : ∀ j w, normAtPlace w (evI F (y l j)) ≤ s := fun j w =>
          (Finset.single_le_sum (fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ w)).trans
            (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)))
              (fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ j))
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _
        have : ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ ≤ s * K := by
          rw [hK, Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_

          conv_lhs => rw [e2 l, map_sum]
          rw [Finset.mul_sum]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_piInf_smul hB.cm]
          exact mul_le_mul_of_nonneg_right (hs1 j w) (norm_nonneg _)
        nlinarith
      · refine ⟨_, ⟨_, hl, rfl⟩, fun u hu => ?_⟩
        beta_reduce
        rw [congrArg (· - ∑ j, mk 0 (y l j).2 • τ (Bt j)) (e2 l), ← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← sub_smul, ← smul_assoc, show y l j - mk 0 (y l j).2 = mk (y l j).1 0 from
          Prod.ext (sub_zero _) (sub_self _), at_mk _ u hu, zero_smul]
    · simp only [h5 i _ hl, ContinuousLinearMap.zero_apply, map_zero, zero_mul, enorm_zero, zero_le]

end PositivityTheory.ThKCT.Line

end
end
