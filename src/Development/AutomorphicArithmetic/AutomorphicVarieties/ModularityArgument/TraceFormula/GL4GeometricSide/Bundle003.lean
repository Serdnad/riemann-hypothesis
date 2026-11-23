module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle410
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting

section Sum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_sum (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ), ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, g ∉ S → F g = 0) → ∫ g, F g ∂μ = ∑ x ∈ T, c x * F (r x) :=
  _root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS

end Sum

section Ops

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem atW_val (w v : InfinitePlace E) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    atW w X a b v = (if v = w then X else 1) a b := by
  simp only [atW]
  split_ifs <;> rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_mul (w w' v : InfinitePlace E) (X Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' Y)) a b v =
      ((if v = w then X else 1) * (if v = w' then Y else 1)) a b := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_inv (w : InfinitePlace E) {X Y : Matrix (Fin n) (Fin n) ℂ} (h : X * Y = 1) :
    (Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w Y) = 1 := by
  ext a b v
  rw [of_atW_mul]
  by_cases hv : v = w
  · simp only [if_pos hv, h]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · simp only [if_neg hv, mul_one]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

private def yAt (w : InfinitePlace E) (k : Un n) : GL (Fin n) (Cinf E) where
  val := Matrix.of (atW w k.1)
  inv := Matrix.of (atW w (star k.1))
  val_inv := of_atW_inv w (Unitary.mul_star_self_of_mem k.2)
  inv_val := of_atW_inv w (Unitary.star_mul_self_of_mem k.2)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem yAt_comm {w w' : InfinitePlace E} (h : w ≠ w') (k k' : Un n) : yAt w k * yAt w' k' = yAt w' k' * yAt w k := by
  apply Units.ext
  ext a b v
  show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v =
    ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v
  rw [of_atW_mul, of_atW_mul]
  by_cases h1 : v = w
  · have h2 : v ≠ w' := h1 ▸ h
    simp [h1, h]
  · simp [h1]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem coord_atW {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (X : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : coord τ (atW w X a b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]
  split_ifs <;> simp

private theorem commute_rt_Eop {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (k : Un n) (a b : Fin n) :
    Commute (Eop τ a b) (rt E n (infGL E n (yAt w k))) := by
  have e := GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b
  have c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q := coord_atW h k.1
  have c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q :=
    coord_atW h (star k.1)
  simp only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  exact e.symm

private theorem commute_Eop_fin (τ : E →+* ℂ) (a b : Fin n) (g : GL (Fin n) (Af E)) :
    Commute (Eop τ a b) (finRep E n g) := by
  have hl : ∀ x, Commute (lieS E n a b x) (finRep E n g) := fun x => by
    rw [lieS_apply]
    exact lie_rt_fin _ g
  have e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I)) := by
    rw [lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact ((hl _).sub_left ((hl _).smul_left _)).smul_left _

private theorem commute_rt_fin (y : GL (Fin n) (Cinf E)) (g : GL (Fin n) (Af E)) :
    Commute (rt E n (infGL E n y)) (finRep E n g) := by
  show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem exists_op [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (K : Subgroup (GL (Fin n) (Af E)))
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧
      ∀ ψ : Sm E n, (∀ k ∈ K, finRep E n k ψ = ψ) → heckeOp μf h ψ.1 = (A ψ).1 := by
  obtain ⟨T, r, c, H⟩ := exists_sum μf K hKo hKc hh.1
  refine ⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩
  · exact Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _
  · funext x
    have e := H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)
    · refine e.trans ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc]
      rfl
    · have e1 : h (g * k) = h g := by simpa using hh.2 1 K.one_mem k hk g
      have e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g) :=
        congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)
      simp only [e1, map_mul, ← mul_assoc, e2]
    · simp [image_eq_zero_of_notMem_tsupport hg]

end Ops

theorem rlComm : RlComm := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hinj : Function.Injective ι := π.V.injective_subtype.comp D.inj
  have lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) →
      (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B := fun A B A' B' hA hB hc =>
    LinearMap.ext fun u => hinj <| by
      have := LinearMap.congr_fun hc.eq (ι u)
      simp only [Module.End.mul_apply] at this ⊢
      rw [hA, hB, hB, hA, this]
  have h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u) := fun w a b u => D.hE1 w a b u
  have h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u) :=
    fun w a b u => D.hE2 w a b u
  have h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u) := fun w k u =>
    Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))
  have h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n),
      (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u) := fun h => by
    obtain ⟨A, hA, hA'⟩ := exists_op μf K hKo hKc h.2
    exact ⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩
  have mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding
  have mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w := fun w => by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ' := fun h e => h (e ▸ rfl)
  refine ⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩
  · exact lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)
  · exact lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))
  · exact lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))
  · exact lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)
  · exact lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))
  · refine (lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq
    show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)

end UpperTheory.V.Z.GSp4Splitting
end
end

section

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open Matrix

private theorem flow {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (c : ℝ → S) (hc : ∀ t, HasDerivAt c (D (c t)) t) :
    c 1 = NormedSpace.exp D (c 0) := by
  have hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t := by
    intro t
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t
    have h := he.clm_apply (hc t)
    convert h using 1
    simp [ContinuousLinearMap.mul_apply]
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0
  simpa using hconst

private theorem exp_mem {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (M : Submodule ℝ S) (hM : IsClosed (M : Set S)) (hD : ∀ y ∈ M, D y ∈ M)
    {x : S} (hx : x ∈ M) : NormedSpace.exp D x ∈ M := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D
  have hs2 := (ContinuousLinearMap.apply ℝ S x).hasSum hs
  have hpow : ∀ m : ℕ, (D ^ m) x ∈ M := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact hD _ ih
  refine hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)
  refine M.sum_mem fun m _ => ?_
  simpa using M.smul_mem _ (hpow m)

private theorem lift {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {S : Submodule ℂ V}
    {c : ℝ → S} {d : S} {t : ℝ} (h : HasDerivAt (fun s => (c s : V)) (d : V) t) : HasDerivAt c d t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  exact (Asymptotics.isLittleO_norm_left).1 h.norm_left

variable {n : ℕ}

private def curve (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) : Un n :=
  ⟨NormedSpace.exp ((t : ℂ) • X), (UpperTheory.RealTr.skewExp n).1 _ (by
    rw [conjTranspose_smul, hX]; simp)⟩

private theorem curve_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    curve X hX (s + t) = curve X hX s * curve X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

private theorem curve_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : curve X hX 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
  simp

end UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open UpperTheory.V.Z.GSp4Splitting.LieStabilizer in
theorem UpperTheory.V.Z.GSp4Splitting.lieStab :
    LieStab := by
  intro n V _ _ σ Kf hder N hN k x hx
  obtain ⟨X, hX, hXk⟩ := (UpperTheory.RealTr.skewExp n).2 k
  obtain ⟨S, hfd, hxS, hσS, hKS, hd⟩ := hder.2 x
  haveI : FiniteDimensional ℂ S := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : Module.End ℂ V := ∑ a, ∑ b, X a b • Kf a b
  have hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w := by
    intro w
    simp [L, LinearMap.sum_apply]
  have hLS : ∀ w ∈ S, L w ∈ S := by
    intro w hw
    rw [hLapp]
    exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)
  have hLN : ∀ w ∈ N, L w ∈ N := by
    intro w hw
    rw [hLapp]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)
  let Dc : S →L[ℂ] S := LinearMap.toContinuousLinearMap (L.restrict hLS)
  let D : S →L[ℝ] S := Dc.restrictScalars ℝ
  have hDapp : ∀ w : S, ((D w : S) : V) = L w := fun w => rfl
  let γ := curve X hX
  let c : ℝ → S := fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩
  have hc : ∀ t, HasDerivAt c (D (c t)) t := by
    intro t
    apply lift
    have h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t) := by
      rw [sub_self, hLapp]
      exact hd X γ (fun _ => rfl) _ (c t).2
    have h1 := h0.comp_sub_const t t
    convert h1 using 1
    funext s
    have : γ s = γ (s - t) * γ t := by
      rw [← curve_add, sub_add_cancel]
    show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)
    rw [this, map_mul, Module.End.mul_apply]
    exact hDapp _
  have h1 := flow D c hc
  let M : Submodule ℂ S := N.comap S.subtype
  have hMc : IsClosed (M : Set S) := Submodule.closed_of_finiteDimensional M
  have hc0 : c 0 ∈ M.restrictScalars ℝ := by
    show σ (γ 0) x ∈ N
    have : γ 0 = 1 := curve_zero X hX
    rw [this, map_one]
    exact hx
  have h2 := exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0
  rw [← h1] at h2
  have hk : γ 1 = k := by
    apply Subtype.ext
    show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1
    simpa using hXk
  have h3 : σ (γ 1) x ∈ N := h2
  rwa [hk] at h3
end
end

section

noncomputable section

open NumberField Matrix Finset
open GlobalTheory.CuspRep
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

section Avg

variable {K M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]

private theorem exists_avg [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (ρ : K →* Module.End ℂ M)
    (hs : ∀ m, IsOpen {k | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ m k, ρ k (P m) = P m) ∧ (∀ m, (∀ k, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ k m, T (ρ k m) = ρ k (T m)) → ∀ m, T (P m) = P (T m) :=
  _root_.UpperTheory.Reformulated.B.ExistsAverage.exists_avg ρ hs

end Avg

section Core

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem fin_op (π : CuspSub E n) (g k : GL (Fin n) (Af E)) (x : π.V) :
    π.finPart g (π.op (.fin k) x) = π.finPart (g * k) x :=
  Subtype.ext (by
    show finRep E n g (finRep E n k x.1) = finRep E n (g * k) x.1
    rw [map_mul, Module.End.mul_apply])

private theorem lie_fin (π : CuspSub E n) (X : Lie E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.lie X) (π.finPart g x) = π.finPart g (π.op (.lie X) x) :=
  Subtype.ext (LinearMap.congr_fun (lie_rt_fin X g) x.1)

private theorem cpt_fin (π : CuspSub E n) (c : Kinf E n) (g : GL (Fin n) (Af E)) (x : π.V) :
    π.op (.cpt c) (π.finPart g x) = π.finPart g (π.op (.cpt c) x) :=
  Subtype.ext (by
    have h := congrArg (rt E n) (infGL_comm (Unitary.toUnits c) g)
    rw [map_mul, map_mul] at h
    exact LinearMap.congr_fun h x.1)

private theorem eop_fin (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) (g : GL (Fin n) (Af E)) (x : π.V) :
    PositivityTheory.S2.Clozel.EopV π τ i j (π.finPart g x) = π.finPart g (PositivityTheory.S2.Clozel.EopV π τ i j x) := by
  simp only [PositivityTheory.S2.Clozel.EopV, LinearMap.smul_apply, LinearMap.sub_apply, lie_fin, map_smul, map_sub]

private theorem core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    (v0 ψ : π.V) (hv0 : v0 ≠ 0) (hfix : ∀ k ∈ K, π.finPart k v0 = v0) (hψ : ψ ≠ 0) :
    ∃ v : π.V, v ≠ 0 ∧ (∀ k ∈ K, π.finPart k v = v) ∧ ∀ (T : Module.End ℂ π.V) (c : ℂ),
      (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → T ψ = c • ψ → T v = c • v := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let ρ : K →* Module.End ℂ π.V := MonoidHom.comp π.finPart K.subtype
  have hρ : ∀ (k : K) m, ρ k m = π.finPart k.1 m := fun _ _ => rfl
  have hs : ∀ m, IsOpen {k : K | ρ k m = m} := fun m => by
    have h1 := (π.cusp m.1 m.2).1.level
    convert h1.preimage continuous_subtype_val using 1
    ext k
    exact Subtype.ext_iff
  obtain ⟨P, hPinv, hPfix, hPT⟩ := exists_avg ρ hs
  have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) →
      ∀ m, T (P m) = P (T m) := fun T hT => hPT T fun k m => hT k.1 m
  let W0 : Submodule ℂ π.V := ⨅ g, LinearMap.ker (P ∘ₗ π.finPart g)
  have mem : ∀ x, x ∈ W0 ↔ ∀ g, P (π.finPart g x) = 0 := fun x => by
    simp [W0, Submodule.mem_iInf]
  have stable : _root_.GlobalTheory.CuspRep.IsStable (W0.map π.V.subtype) := by
    rintro o _ ⟨x, hx, rfl⟩
    refine ⟨π.op o x, ?_, rfl⟩
    have hx' := (mem x).1 hx
    refine (mem _).2 fun g => ?_
    cases o with
    | fin k => rw [fin_op]; exact hx' _
    | cpt c => rw [← cpt_fin, ← hcomm _ (fun g x => cpt_fin π c g x), hx', map_zero]
    | lie X => rw [← lie_fin, ← hcomm _ (fun g x => lie_fin π X g x), hx', map_zero]
  rcases π.irred _ (Submodule.map_subtype_le _ _) stable with h | h
  · have hn : ψ ∉ W0 := fun hm => by
      have h1 : ψ.1 ∈ W0.map π.V.subtype := ⟨ψ, hm, rfl⟩
      rw [h, Submodule.mem_bot] at h1
      exact hψ (Subtype.ext h1)
    rw [mem] at hn
    push_neg at hn
    obtain ⟨g, hg⟩ := hn
    refine ⟨P (π.finPart g ψ), hg, fun k hk => hPinv _ ⟨k, hk⟩, fun T c hT hc => ?_⟩
    rw [hcomm T hT, hT, hc, map_smul, map_smul]
  · exfalso
    have h1 : v0.1 ∈ W0.map π.V.subtype := by
      rw [h]
      exact v0.2
    obtain ⟨y, hy, e⟩ := h1
    have hy0 : y = v0 := Subtype.ext e
    subst hy0
    have h2 := (mem y).1 hy 1
    rw [map_one, Module.End.one_apply, hPfix y fun k => hfix k.1 k.2] at h2
    exact hv0 h2

end Core

theorem rlLow : HeckeMem → LowType → RlLow := by
  intro _ hL
  unfold RlLow ForRl
  intro E _ _ _ n hn π _ K _ hKc _ _ _ μf _ D hreg hnt w lam hanti hch
  obtain ⟨ν, ψ, hψ, hψ0, hk, hc⟩ := hL E n hn π hreg w lam hanti hch
  obtain ⟨u0, hu0⟩ := exists_ne (0 : D.U)
  have hv0 : D.i u0 ≠ 0 := fun e => hu0 (D.inj (by rw [e, map_zero]))
  have hfix0 : ∀ k ∈ K, π.finPart k (D.i u0) = D.i u0 := fun k hk' =>
    Subtype.ext ((D.rng (D.i u0)).1 ⟨u0, rfl⟩ k hk')
  let ψ' : π.V := ⟨ψ, hψ⟩
  have hψ' : ψ' ≠ 0 := fun e => hψ0 (congrArg Subtype.val e)
  obtain ⟨v, hv, hfix, hT⟩ := core π K hKc (D.i u0) ψ' hv0 hfix0 hψ'
  obtain ⟨u, hu⟩ := (D.rng v).2 fun k hk' => congrArg Subtype.val (hfix k hk')
  have hune : u ≠ 0 := fun e => hv (by rw [← hu, e, map_zero])
  let T : Fin n → Fin n → Module.End ℂ π.V := fun a b =>
    PositivityTheory.S2.Clozel.EopV π w.embedding a b - PositivityTheory.S2.Clozel.EopV π (ComplexEmbedding.conjugate w.embedding) b a
  have hTval : ∀ a b (x : π.V), (T a b x).1 = eopW w true a b x.1 - eopW w false b a x.1 := fun a b x => by
    simp [T, eopW, GlobalTheory.CompanionTheory.ClozelPurity.EopV_val]
  have hTc : ∀ a b g (x : π.V), T a b (π.finPart g x) = π.finPart g (T a b x) := fun a b g x => by
    simp only [T, LinearMap.sub_apply, eop_fin, map_sub]
  have hTu : ∀ a b, D.i (kF (D.E1 w) (D.E2 w) a b u) = T a b v := fun a b => Subtype.ext (by
    rw [hTval, ← hu]
    simp only [kF, LinearMap.add_apply, map_add (f := _), Submodule.coe_add, D.hE1, D.hE2]
    abel)
  have hmem : u ∈ hwSp (D.E1 w) (D.E2 w) ν := by
    refine ⟨fun a => D.inj ?_, fun a b hab he => D.inj ?_⟩
    · have h1 : T a a ψ' = (ν a : ℂ) • ψ' := Subtype.ext (by
        rw [hTval]
        exact hk.1 a)
      rw [hTu, hT _ _ (hTc a a) h1, map_smul, hu]
    · have h1 : T a b ψ' = (0 : ℂ) • ψ' := Subtype.ext (by
        rw [hTval, zero_smul]
        exact hk.2 a b hab he)
      rw [hTu, hT _ _ (hTc a b) h1, zero_smul, map_zero]
  exact ⟨ν, fun e => hune (by
    have h1 := hmem
    rw [e, Submodule.mem_bot] at h1
    exact h1), hc⟩

end UpperTheory.V.Z.GSp4Splitting
end
end
