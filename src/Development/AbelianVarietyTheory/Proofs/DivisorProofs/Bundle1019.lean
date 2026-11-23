module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Formalism.LocalRingCardinality.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle994
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Columns.Bundle013
public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
import Formalism.LocalRingCardinality.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenFibre

local instance (priority := high) grpObjPullback {S T : Scheme.{0}} (f : T ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

theorem jK_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V)
    (hemb : ∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W →
      emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) :
    jK V ≫ ξ = spMap emb ≫ M.pt := by
  obtain ⟨W, hW, hξ, -⟩ := GlobalTheory.Points.exists_isAffineOpen_le ξ (GlobalTheory.Points.le_preimage_top ξ)
  have hz : ξ (IsLocalRing.closedPoint V) ∈ W := hξ (x := IsLocalRing.closedPoint V) trivial
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨_, hz⟩
  refine GlobalTheory.Points.ext_of_valR hW (GlobalTheory.Points.le_preimage_comp (V := ⊤) (jK V) ξ hξ le_rfl)
    (GlobalTheory.Points.le_preimage_comp (V := ⊤) (spMap emb) M.pt hpt le_rfl) fun f => ?_
  calc valR (jK V ≫ ξ) W f = algebraMap V (FractionRing V) (valR ξ W f) :=
        GlobalTheory.Points.valR_spMap_comp (algebraMap V (FractionRing V)) ξ W hξ f
    _ = emb (valF M.pt W f) := (hemb W f hz).symm
    _ = valR (spMap emb ≫ M.pt) W f := (GlobalTheory.Points.valR_spMap_comp emb M.pt W hpt f).symm

theorem genFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∀ [IsCommMonObj ((Over.pullback ξ).obj Zh.G)] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (IsLocalRing.maximalIdeal V) D A ((Over.pullback ξ).obj Zh.G)), LBIso U.LG.L (Zh.L.L.pull (pullback.fst Zh.G.hom ξ)) → ∀ (emb : Ω →+* FractionRing V), (∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W → emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) → ∃ φ : A.A.left ⟶ ρ.P.A.left, IsGrpPullback A.A ρ.P.A (spMap (emb.comp (algebraMap S.R Ω))) φ ∧ LBIso A.L (ρ.P.L.pull φ) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO V _ _ _ ξ _ _ D A U hLG emb hemb
  have e₁ := jK_comp_eq M ξ emb hemb
  have hpt : Set.range M.pt ⊆ (U₀ : Set M.Z) := fun _ ⟨w, hw⟩ => hw ▸ M.top_le_preimage_pt hO.ne (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hpt)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ Zh.u₀ = spMap S.R.val.toRingHom := Zh.u₀_gen x hx
  let y : Sp (FractionRing V) ⟶ U₀.toScheme := spMap emb ≫ x
  have e₂ : (𝟙 _ ≫ jK V) ≫ ξ = y ≫ U₀.ι := by
    rw [Category.id_comp, e₁, Category.assoc, hx]
  have e₃ : 𝟙 _ ≫ y ≫ Zh.u₀ = spMap (emb.comp (algebraMap S.R Ω)) := by
    rw [Category.id_comp, Category.assoc, hxu]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  have hA := ((isGrpPullback_of_iso U.gen.symm).comp
    (isGrpPullback_pullback ((Over.pullback ξ).obj Zh.G) (jK V))).comp (isGrpPullback_pullback Zh.G ξ)
  have hB := (isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp Zh.cart
  obtain ⟨e, he, hφ⟩ := grpPullback_iso (hA.congr e₂ rfl) hB
  haveI := he
  have hC := (isGrpPullback_of_iso e).comp ((isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) y).comp
    (isGrpPullback_pullback ρ.P.A Zh.u₀))
  refine ⟨_, hC.congr e₃ rfl, ?_⟩
  have H1 := U.ext
  have H2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLG (pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V)) rfl
  have H3 := LBIso.trans (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (pull_isLB Zh.L.isLB _) H1 H2
  have H4 : LBIso (A.L.pull (𝟙 _)) (Zh.L.L.pull (U.gen.inv.left ≫
      pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫ pullback.fst Zh.G.hom ξ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp U.gen.inv.left
      (by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]) rfl H3
  have H5 := LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl) (chartPullId _) H4
  have H6 : LBIso (Zh.L.L.pull (U.gen.inv.left ≫ pullback.fst ((Over.pullback ξ).obj Zh.G).hom (jK V) ≫
      pullback.fst Zh.G.hom ξ)) (ρ.P.L.pull (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y ≫
      pullback.fst ρ.P.A.hom Zh.u₀)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e.hom.left ≫ pullback.fst ((Over.pullback Zh.u₀).obj ρ.P.A).hom y)
      (a := Zh.φ) (b := pullback.fst ρ.P.A.hom Zh.u₀) (by rw [Category.assoc, hφ, Category.assoc]; rfl)
      (Category.assoc _ _ _).symm ⟨Zh.w, Zh.w_gen⟩
  exact LBIso.trans A.isLB (pull_isLB Zh.L.isLB _) (pull_isLB ρ.P.isLB _) H5 H6

end GlobalTheory.GenFibre
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.LevelCoprime

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x
  exact h1.trans (phi_conj H H.φ₀ (σ x)).symm

theorem b_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_b : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [phi_conj, map_neg, h3]
  simp

theorem agree_on_K (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = τ H.sqrtMinusD) (x : H.E) (hx : x ∈ H.K) :
    σ x = τ x := by
  have hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem trace_rat (x : H.E) (hx : x ∈ H.K) : ∃ r : ℚ, algebraMap ℚ H.E r = x + H.conj x := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E) := by
    rw [← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro σ _
    have hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [← map_pow, b_sq, map_neg, map_natCast]
    rw [map_add (f := _), sigma_conj]
    rcases hb with hb | hb
    · have := agree_on_K H σ 1 hb x hx
      rw [this]; rfl
    · have := agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx
      rw [this, conj_conj, add_comm]
  exact IntermediateField.mem_bot.1 hmem

theorem trace_int (x : 𝓞 H.E) (hx : (x : H.E) ∈ H.K) : ∃ a : ℤ, (a : H.E) = x + H.conj x := by
  obtain ⟨r, hr⟩ := trace_rat H x hx
  have h1 : IsIntegral ℤ (H.conj (x : H.E)) :=
    IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe
  have h2 : IsIntegral ℤ (algebraMap ℚ H.E r) := hr ▸ x.isIntegral_coe.add h1
  have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  rw [← hr, ← ha]
  simp

theorem trace_sq_le (x : H.E) (a : ℤ) (T : ℕ) (ha : (a : H.E) = x + H.conj x) (hT : x * H.conj x = T) :
    a ^ 2 ≤ 4 * T := by
  have h1 := congrArg H.φ₀ ha
  have h2 := congrArg H.φ₀ hT
  rw [map_add (f := _), phi_conj, map_intCast, Complex.add_conj] at h1
  rw [map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply] at h2
  have h3 : (a : ℝ) = 2 * (H.φ₀ x).re := by exact_mod_cast h1
  have h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ) := by exact_mod_cast h2
  have h5 : (a : ℝ) ^ 2 ≤ 4 * T := by
    rw [h3, ← h4]
    nlinarith [mul_self_nonneg (H.φ₀ x).im]
  exact_mod_cast h5

end Host

theorem four_dvd {E : Type} [Field E] [NumberField E] (n : ℤ) (y : E) (hy : IsIntegral ℤ y)
    (h : (n : E) = 4 * y) : (4 : ℤ) ∣ n := by
  have h1 : y = algebraMap ℚ E ((n : ℚ) / 4) := by
    rw [map_div₀, map_intCast, h]
    simp
  rw [h1] at hy
  have h3 := (isIntegral_algebraMap_iff ).1 hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  have h4 : (a : ℚ) = (n : ℚ) / 4 := by simpa using ha
  have h5 : (n : ℚ) = 4 * a := by rw [h4]; ring
  exact_mod_cast h5

theorem not_dvd_trace {D : D7} (X : ErrX D) (u : D.what₂.Word) (a : ℤ)
    (ha : (a : D.host.E) = X.piT u + D.host.conj (X.piT u)) : ¬ (((D.mem u).A.T : ℤ) ∣ a) := by
  intro hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b := by
    have h4 : (4 : ℕ) ∣ D.host.QS :=
      (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h4
    refine ⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩
    rw [hk] at hc
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  have hle := trace_sq_le D.host _ a _ ha hn
  have hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E) := by
    rw [hb]; simp [map_ofNat]
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe
  have hb0 := b.isIntegral_coe
  rw [hb'] at ha hn
  simp only [map_add (f := _), map_mul, map_one, map_ofNat] at ha hn
  have h1 : (4 : ℤ) ∣ a - 2 := four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)
  have h4 : IsIntegral ℤ (4 : D.host.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))
  have h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 :=
    four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)
  have h3 := (D.mem u).A.T_prime.two_le
  obtain ⟨k, rfl⟩ := hd
  set T : ℤ := ((D.mem u).A.T : ℤ) with hT
  have h5 : 5 ≤ T := by omega
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 1 ≤ k ^ 2 := by
    have := sq_pos_of_ne_zero hk
    omega
  nlinarith [mul_pow T k 2]

theorem coprime_conj {D : D7} (X : ErrX D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    ¬ (0 < vAdd (D.plEq w) (D.embE (X.piT u : D.host.E)) ∧
      0 < vAdd (D.plEq w) (star (D.embE (X.piT u : D.host.E)))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := trace_int D.host (X.piT u) (X.piT_K u)
  have hp := (D.mem u).A.T_prime
  have hn := X.piT_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [← hn] at hT0
  rw [← D.embE_conj] at h2
  have i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E)) :=
    IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe
  have i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E))) :=
    IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe
  let y : 𝓞 D.what₂.LL := ⟨_, i1⟩
  let z : 𝓞 D.what₂.LL := ⟨_, i2⟩
  have hy : y ≠ 0 := fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have m1 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1
  have m2 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2
  have e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z := by
    apply RingOfIntegers.coe_injective
    rw [map_intCast, map_add (f := _)]
    change _ = D.embE _ + D.embE _
    rw [← map_add (f := _), ← ha, map_intCast]
  have m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := e ▸ Ideal.add_mem _ m1 m2
  have m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := hw ▸ resChar_mem D w
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)
  obtain ⟨s, t, hst⟩ := hc
  apply (D.plEq w).isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst
  push_cast at h
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)

end GlobalTheory.LevelCoprime
end

section

noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.DIV
  _root_.Formalism.L2.Col _root_.Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open scoped ComplexOrder

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OpLe (S S' : GSD K) (v : InfinitePlace K) (T : S.V →ₗ[K] S'.V) (t : ℝ) : Prop :=
  ∀ x : S.V, (S'.pairAt v (T x) (T x)).re ≤ t * (S.pairAt v x x).re

def PosAt (S : GSD K) (v : InfinitePlace K) : Prop := (S.gramV.map v.embedding).PosSemidef

end Ops

section Coef

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def sqAt (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (σ ((bVV K lam).repr x i)) *
    σ (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j)) * σ ((bVV K lam).repr x j)).re

def CoefOpLe (σ : K →+* ℂ) {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') (t : ℝ) : Prop :=
  ∀ x, sqAt σ lam' (T x) ≤ t * sqAt σ lam x


open Classical in
def degAt {a b : ℕ} (e : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

end Coef

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

def LocSmall (q : ℕ) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ y ∈ M, x y ∈ M') ∧ (∀ x z : HomE E a b, (∀ y ∈ M, z y ∈ M') → Φ (x + (q : E) • z) = Φ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Φ x)‖ ≤ β

def SmallDatum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)
    (Ξ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ homAt S N N') ∧ (∀ x, ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Ξ x)‖ ≤ β

end Data

def Pres (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (y : Fin k → TaylorLogMetric.VC D a b), (∀ i, r i ∈ TaylorLogMetric.Qbar) ∧ (∀ i, StandardLatticesGL3.LaQ D T L L' (y i)) ∧
    (∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ∑ i, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i)‖ ≤ n) ∧ F = StandardLatticesGL3.comb D T r y G

def toHost {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun w => F fun τ => w (s.iT τ)

def supConst (D : D7) (a b : ℕ) : ℝ :=
  3 * (2 * ((TaylorLogMetric.fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (TaylorLogMetric.fF D * a * b)

def errUnit (N : NumDatum) (T : ℕ) : ℝ :=
  N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)

def FamilyTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → StandardLatticesGL3.natTie D cc δ (B.eNat χ)

def FamilyVectors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.VecP χ

def FamilyNorms : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.ThP C χ

def PeriodLattices : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    TaylorLogMetric.IsChi D χ → IsDgen D cD → B.kc.YFinite → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))), Even a → Even b →
    (∀ P ∈ S, conjPrime₂ P ∉ S) → (ambOf s B χ cD).AAUnit S → (ambOf s B χ cD).LaHyp a b S

def CosetRefinement : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ), X.Ok →
    (∀ P ∈ S, (2 : 𝓞 X.E) ∉ P.asIdeal) → Odd Md → A.LaHyp a b S → A.IndAdd a b S Md

end GlobalTheory.ColNorms
end
end

section

noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩


open Classical in
def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem buRat_of_coordinates : ∀ (D : D7) (μ : D.what₂.Tup), μ = D.what₂.mu0 → ∀ {n nV d : ℕ} (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (a : D.what₂.Word → ℕ) (eNu : ∀ u, (Fin (a u) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Formalism.BasicNotions.Rows.BuDefQ D.what₂ → (∀ x y, ⟪jA x, jA y⟫_ℂ ∈ Set.range D.what₂.embLL) → D.what₂.V0 μ = Submodule.span ℂ (Set.range fun F0 => jA (V.mulVec F0)) → (∀ F0, D.what₂.iota μ (jA (V.mulVec F0)) = D.jEE (eRR (Pq.mulVec F0))) → Function.Surjective Pq.mulVec → (∀ u x F0, D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec F0)) ∈ Set.range D.what₂.embLL) → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro D μ hμ n nV d jA V Pq eRR a eNu hB hinner hV hι hPq hper
  subst hμ
  intro u φ x
  obtain ⟨x', rfl⟩ := (eNu u).surjective φ
  obtain ⟨y, rfl⟩ := eRR.surjective x
  obtain ⟨G, rfl⟩ := hPq y
  have key := span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hset : {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0} = ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL)) := by
    ext z
    simp
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL))) := by
    rw [← hset, ← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  obtain ⟨G', hG', hperp⟩ := GlobalTheory.T.exists_rational_orthogonal_projection_semilinear D.what₂.LL D.what₂.embLL (D.what₂.Amb D.what₂.mu0) nV (jA.comp V.mulVecLin)
    (fun x y => hinner _ _) (LinearMap.ker Pq.mulVecLin) G
  have hG'0 : Pq.mulVec G' = 0 := hG'
  set q : D.what₂.Amb D.what₂.mu0 := jA (V.mulVec (G - G')) with hq
  have hqeq : q = (jA.comp V.mulVecLin) G - (jA.comp V.mulVecLin) G' := by
    rw [hq, ← map_sub]
    rfl
  have hqV : q ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G - G', rfl⟩
  have hqU : q ∈ (D.what₂.Usp D.what₂.mu0)ᗮ := by
    rw [hU, hqeq]
    exact hperp
  have hqQ : q ∈ D.what₂.Qsp D.what₂.mu0 := ⟨hqV, hqU⟩
  have hιq : D.what₂.iota D.what₂.mu0 q = D.jEE (eRR (Pq.mulVec G)) := by
    rw [hq, hι, Matrix.mulVec_sub, hG'0, sub_zero]
  obtain ⟨z, hz⟩ := hper u x' (G - G')
  refine ⟨z, ?_⟩
  rw [hB u, ← hιq, D.what₂.sec_iota _ q hqQ, hz]

end GlobalTheory
end
