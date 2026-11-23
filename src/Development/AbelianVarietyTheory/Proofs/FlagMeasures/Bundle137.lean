module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle016
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.LayerBox

theorem pres_uncurry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) volume volume := by
  have hm : Measurable (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (x : ι → κ → ℝ) (p : ι × κ) => x p.1 p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b))) := by
    ext y; simp [Set.mem_pi]
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp [volume_pi_pi]

theorem pres_layers (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (h : ι → ∀ i, deg i < m) :
    MeasurePreserving (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) volume volume := by
  have hm : Measurable (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) := by
    fun_prop
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun c => Set.univ.pi (fun v => Set.univ.pi (fun i => s (v, i.1)))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Prod.forall]
    constructor
    · rintro H ⟨c, hc⟩ v ⟨i, hi⟩
      simp only at hi
      subst hi
      exact H v i
    · intro H v i
      exact H ⟨deg i, h v i⟩ v ⟨i, rfl⟩
  rw [this, volume_pi_pi, Fintype.prod_prod_type]
  simp only [volume_pi_pi]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun i => (⟨deg i, h v i⟩ : Fin m))]
  refine Finset.prod_congr rfl fun c _ => ?_
  symm
  apply Finset.prod_subtype (f := fun i => volume (s (v, i)))
  intro i
  simp [Fin.ext_iff]

theorem volume_layer_box : ∀ (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (ι → ∀ i, deg i < m) → (∀ c, MeasurableSet (D c)) → volume {x : ι → Fin d → ℝ | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} = ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ d m deg D h hD
  let F : Set (ι × Fin d → ℝ) :=
    {z | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ∈ D c}
  have hF : MeasurableSet F := by
    have : F = ⋂ c, ⋂ (_ : c < m),
        (fun (z : ι × Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => z (v, i.1)) ⁻¹' D c := by
      ext z; simp [F]
    rw [this]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (hD c).preimage (by fun_prop)
  have h1 := (pres_uncurry ι (Fin d)).measure_preimage hF.nullMeasurableSet
  have h2 := (pres_layers ι d m deg h).measure_preimage hF.nullMeasurableSet
  have key : ∀ (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (c : ℕ) (hc : c < m),
      (fun v (i : {i : Fin d // deg i = c}) => y ⟨deg i.1, h v i.1⟩ v ⟨i.1, rfl⟩) = y ⟨c, hc⟩ := by
    intro y c hc
    funext v i
    obtain ⟨i, hi⟩ := i
    subst hi
    rfl
  have h3 : (fun (y : ∀ c : Fin m, ι → {i : Fin d // deg i = c} → ℝ) (p : ι × Fin d) =>
      y ⟨deg p.2, h p.1 p.2⟩ p.1 ⟨p.2, rfl⟩) ⁻¹' F = Set.univ.pi (fun c : Fin m => D c) := by
    ext y
    simp only [F, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro H c
      have := H c c.2
      rwa [key y c c.2] at this
    · intro H c hc
      rw [key y c hc]
      exact H ⟨c, hc⟩
  rw [h3, volume_pi_pi, Fin.prod_univ_eq_prod_range (fun c => volume (D c))] at h2
  rw [h2, ← h1]
  rfl

end GlobalTheory.LayerBox
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem measurePreserving_layer_shear (d : ℕ) (p : Fin d → Prop) [DecidablePred p]
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, ¬ p i → (∀ k, p k → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i)
      (volume : Measure (Fin d → ℝ)) volume := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  have he_mp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p

  let G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ) := fun a i => f (e.symm (a, 0)) i
  have hG : Measurable G := by
    refine Measurable.of_eval (fun i => ?_)
    exact (measurable_pi_apply (i : Fin d)).comp
      (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))

  have hΨ : MeasurePreserving
      (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a)
      (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst))
      (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)
  have key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) =
      e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e := by
    funext x i
    have hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k := fun k hk => by simp [e, hk]
    by_cases hi : p i
    · simp [e, hi]
    · simp [e, G, hi, h x _ i hi hx]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)

theorem measurePreserving_triangular_shear (d : ℕ) (deg : Fin d → ℕ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by

  let U : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun n x i => if n ≤ deg i then x i + f x i else x i
  have hS : ∀ n, MeasurePreserving
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume :=
    fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf
      (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))
  have hstep : ∀ n, U n =
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1) := by
    intro n
    funext x i
    by_cases hin : deg i = n
    · have hfx : f (U (n + 1) x) i = f x i :=
        h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])
      simp only [Function.comp_apply, hfx]
      simp only [U]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.comp_apply, U]
      rw [if_pos hin]
      by_cases h2 : n ≤ deg i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hN : ∀ n, Finset.univ.sup deg < n → U n = id := by
    intro n hn
    funext x i
    have hi : deg i ≤ Finset.univ.sup deg := Finset.le_sup (Finset.mem_univ i)
    simp only [U, id]
    rw [if_neg (by omega)]
  have hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [hN n (by omega)]
      exact MeasurePreserving.id _
    | succ k ih =>
      intro n hn
      rw [hstep n]
      exact (hS n).comp (ih (n + 1) (by omega))
  have h0 : U 0 = fun x => x + f x := by
    funext x i
    simp [U]
  rw [← h0]
  exact hU (Finset.univ.sup deg + 1) 0 (by omega)

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem lintegral_rpow_neg_change_of_variable :
    ∀ (N s : ℝ), 0 < N → 0 < s → ∀ F : ℝ → ENNReal, Measurable F →
      ∫⁻ t in Set.Ioi (0 : ℝ), F ((t / s) ^ (-(1 / N))) / ENNReal.ofReal t =
        ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * ENNReal.ofReal (N / τ) := by
  intro N s hN hs F _
  set a : ℝ := -(1 / N) with ha_def
  have ha : a ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hN.ne')

  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => (t / s) ^ a) (1 / s * a * (t / s) ^ (a - 1))
        (Set.Ioi 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) t := (hasDerivAt_id' t).div_const s
    exact (h1.rpow_const (Or.inl (div_pos ht hs).ne')).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => (t / s) ^ a) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxy' : (x / s) ^ a = (y / s) ^ a := hxy
    have hdiv : x / s = y / s := by
      rw [← Real.rpow_rpow_inv (div_pos hx hs).le ha, ← Real.rpow_rpow_inv (div_pos hy hs).le ha,
        hxy']
    exact (div_left_inj' hs.ne').mp hdiv
  have himage : (fun t : ℝ => (t / s) ^ a) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext τ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.rpow_pos_of_pos (div_pos ht hs) a
    · intro hτ
      refine ⟨s * τ ^ a⁻¹, mul_pos hs (Real.rpow_pos_of_pos hτ _), ?_⟩
      show (s * τ ^ a⁻¹ / s) ^ a = τ
      rw [mul_div_cancel_left₀ _ hs.ne', Real.rpow_inv_rpow (le_of_lt hτ) ha]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun τ => F τ * ENNReal.ofReal (N / τ))
  rw [himage] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := ht
  have hu : 0 < t / s := div_pos ht' hs
  have hua : 0 < (t / s) ^ a := Real.rpow_pos_of_pos hu a

  have hreal : |1 / s * a * (t / s) ^ (a - 1)| * (N / (t / s) ^ a) = t⁻¹ := by
    have hneg : 1 / s * a * (t / s) ^ (a - 1) = -(1 / s * (1 / N) * ((t / s) ^ a / (t / s))) := by
      rw [Real.rpow_sub hu, Real.rpow_one, ha_def]
      ring
    have hpos : 0 < 1 / s * (1 / N) * ((t / s) ^ a / (t / s)) :=
      mul_pos (mul_pos (one_div_pos.mpr hs) (one_div_pos.mpr hN)) (div_pos hua hu)
    rw [hneg, abs_neg, abs_of_pos hpos]
    field_simp
  dsimp only
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos ht', ← hreal,
    ENNReal.ofReal_mul (abs_nonneg _)]
  ring

end GlobalTheory.FlagMeas
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongIndex


open scoped TensorProduct in
theorem quot_smul_top_span_card {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    (∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N), Submodule.span R (Set.range v) = ⊤) ∧
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩
  · have h1 : Submodule.span R (Set.range b) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
        Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    rw [Set.range_comp]
    exact h2
  · rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
      Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_hom_quot_smul_top {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by
  obtain ⟨⟨v, hv⟩, hc⟩ := quot_smul_top_span_card (R := R) (N := N) I
  have : Finite (N ⧸ (I • ⊤ : Submodule R N)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x)
    rw [LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  let Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N)) :=
    fun f i => Submodule.liftQ _ f (hk f) (v i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
      LinearMap.ext_on_range hv fun i => congrFun hfg i
    ext x
    simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)
  refine ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩
  rw [Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]

theorem finrank_le_finrank_span {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) M ≤ Module.finrank K (Submodule.span K (M : Set V)) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl
  have h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f) := hf.map' _ (Submodule.ker_subtype M)
  have h2 : LinearIndependent K (M.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1
  let g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V) :=
    fun i => ⟨f i, Submodule.subset_span (f i).2⟩
  have h3 : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2
  simpa using h3.fintype_card_le_finrank

theorem relIndex_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  intro K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  obtain ⟨hfin, hcard⟩ := card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪
  have hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M := by
    intro s hs x hx
    rw [← hG s hs]
    exact Submodule.smul_mem_pointwise_smul x s M hx
  have hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M := by
    intro s hs x hx
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)
    · rw [LinearMapClass.map_smul_of_tower]
      exact Submodule.smul_mem_smul ha (hmem s hs y hy)
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  let ρ : G → (M →ₗ[𝓞 K] M) := fun s =>
    (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)
  let Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M)) := fun s => (Submodule.mkQ _).comp (ρ s)
  have hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G := by
    intro s t hst
    refine hB _ (s⁻¹ * t).2 fun x hx => ?_
    have h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M) :=
      (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm
    have h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M := by
      have := Submodule.mem_map_of_mem (f := M.subtype) h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
      exact this
    have h3 := hmem' _ (s⁻¹).2 _ h2
    simpa using h3
  let Ψ : G ⧸ B.subgroupOf G → _ := fun q => Φ q.out
  have hΨ : Function.Injective Ψ := by
    intro q q' h
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientGroup.eq.2 (hΦ _ _ h)
  have : Finite (G ⧸ B.subgroupOf G) := Finite.of_injective Ψ hΨ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  refine (Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)

end GlobalTheory.CongIndex
end
