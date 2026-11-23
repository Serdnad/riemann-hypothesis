module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistBaseChange

theorem eq_pullS_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') : s' = GlobalTheory.VVRank.pullS A a h s := by

  exact DVR.SecOps.sec_ext H

theorem isTwistPull_baseChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T T' : Over S) (h : T' ⟶ T) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (ψ' : T' ⊗ A ⟶ T' ⊗ A) (m' : T' ⊗ A ⟶ A) (hm' : ψ' ≫ snd T' A = m'), ψ' ≫ h ▷ A = h ▷ A ≫ ψ → ∀ (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])), α.IsGen → α'.IsGen → LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α (h ▷ A).left) → ∀ (s : LB.Sec (LPow A L b T)) (t : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L b T')) (t' : LB.Sec (LPow A L a T')), IsTwistPull A L ψ m hm a b α s t → IsPullSec A L b (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) t t' → IsTwistPull A L ψ' m' hm' a b α' s' t' := by
  intro S A _ L hL T T' h ψ m hm ψ' m' hm' hψ a b α α' hα hα' hcorr s t s' t' hst hs ht
  obtain rfl := eq_pullS_of_isPullSec A b h hs
  obtain rfl := eq_pullS_of_isPullSec A a h ht

  have e : ψ'.left ≫ (h ▷ A).left = (h ▷ A).left ≫ ψ.left := by
    rw [← Over.comp_left, hψ, Over.comp_left]
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' (fun y J hJ => ?_)

  have hv : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hcorr _).trans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ α _ _)
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ,
    GlobalTheory.VVRank.sv_of_isTwistPull A hst _ y hJ, hv]
  simp only [Category.id_comp, e]

end GlobalTheory.TwistBaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory


open MvPolynomial in
theorem map_lap_one {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k' 1 τ τ' a a' (MvPolynomial.map f P) = MvPolynomial.map f (lap r n k 1 τ τ' a a' P) := by

  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
  Derivation.coeFn_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, pderiv_map]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  congr 2
  by_cases h : b = b' <;> simp [Matrix.one_apply, h]


open MvPolynomial in
theorem map_rowShift {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (σ : T) (i i' : Fin (r σ)) (t : k) (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k' σ i i' (f t) (MvPolynomial.map f P) = MvPolynomial.map f (rowShift r n k σ i i' t P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowShift]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p s hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem map_mem_HHa {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (hf : Function.Surjective f) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n k' cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [map_lap_one, h1 τ hτ b b', map_zero]
  · intro σ i i' hi t
    obtain ⟨s, rfl⟩ := hf t
    rw [map_rowShift, h2 σ i i' hi s]
  · intro m hm
    exact h3 m (MvPolynomial.support_map_subset f P hm)

theorem finrank_le_of_span_sup_smul_top {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ} (x : Fin n → M) (I : Ideal R) (hI : I ≠ ⊤)
    (h : Submodule.span R (Set.range x) ⊔ (I • ⊤ : Submodule R M) = ⊤) : Module.finrank R M ≤ n := by
  set N := Submodule.span R (Set.range x) with hN
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (N := N) (N' := ⊤) (P := ⊤) (I := I) Module.Finite.fg_top le_rfl (by rw [h])
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem hr1
  have hmem : ∀ m : M, (r • (LinearMap.id : M →ₗ[R] M)) m ∈ N := fun m =>
    hr (Submodule.smul_mem_pointwise_smul m r ⊤ Submodule.mem_top)
  have hinj : Function.Injective ((r • (LinearMap.id : M →ₗ[R] M)).codRestrict N hmem) := by
    intro u v huv
    have : r • u = r • v := congrArg Subtype.val huv
    exact smul_right_injective M hr0 this
  haveI : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range x)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank R N ≤ n := by
    simpa [Set.finrank] using finrank_range_le_card (R := R) x
  exact h1.trans h2

theorem Mfr_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Mfr l ≠ ⊤ := by
  intro h
  have hb : l.Mb = ⊤ := by
    rw [Ideal.eq_top_iff_one] at h ⊢
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 h
    have : y = 1 := H.bar.injective (by simpa using hy1)
    exact this ▸ hy
  have hp := l.prod
  rw [hb, Ideal.map_top, Ideal.top_mul] at hp
  have hn := congrArg Ideal.absNorm hp
  rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast] at hn
  have h3 := l.three_le
  have hpos : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  rcases Nat.pow_eq_one.1 hn.symm with h' | h' <;> omega

theorem admissible_columns_le_and_harmonic_map_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw l Xo c n d
  refine ⟨fun rk x0 hx => ?_, fun a P hP => ?_⟩
  swap
  · have hs : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
    generalize (d.eF : c.F →+* d.c₂.F) = f at hs ⊢
    exact map_mem_HHa Dw.mult n f hs _ _ _ P hP
  haveI := Dw.fin
  haveI := Dw.proj
  rw [← Dw.rank]
  refine finrank_le_of_span_sup_smul_top x0 (Mfr l) (Mfr_ne_top l) ?_
  unfold AdmX at hx
  refine top_le_iff.1 (hx.ge.trans ?_)
  exact sup_le_sup_right (Submodule.span_mono (Set.image_subset_range _ _)) _

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dualFamily_of_nsmul_integral {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : 0 < N)
    (hu : ∀ v ∈ L, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b) :
    ∃ (m : ℕ) (w : Fin m → L) (lam : Fin m → (L →ₗ[𝓞 E] 𝓞 E)), ∀ v, ∑ i, lam i v • w i = v := by
  classical
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hfg : L.FG := by
    have hle : L ≤ Submodule.span (𝓞 E)
        (Set.range fun b : Fin n => (Pi.single b (N : E)⁻¹ : Fin n → E)) := by
      intro v hv
      choose u hu' using hu v hv
      have : v = ∑ b, u b • (Pi.single b (N : E)⁻¹ : Fin n → E) := by
        funext c
        rw [Finset.sum_apply, Finset.sum_eq_single c]
        · simp only [Pi.smul_apply, Pi.single_eq_same]
          rw [Algebra.smul_def]
          change v c = (u c : E) * _
          rw [hu']; field_simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb.symm]
        · simp
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ g, fun v => ?_⟩
  have h1 : f (g v) = v := LinearMap.congr_fun hfg v

  conv_rhs => rw [← h1, pi_eq_sum_univ' (g v), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 2

theorem mem_stdLat_iff_integral {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ b, ∃ u : 𝓞 E, (u : E) = v b := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

theorem modN_sq_iff_exists_genLat_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  classical
  intro E _ _ _ H Dw n Λ N hU hN hle a
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have inj : Function.Injective (fun x : 𝓞 E => (x : E)) := RingOfIntegers.coe_injective
  have he : ∀ b : Fin n, (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := by
    intro b
    apply hle
    have h1 : (Pi.single b (1 : E) : Fin n → E) ∈ stdLat E n := by
      rw [mem_stdLat_iff_integral]
      intro c
      by_cases h : c = b
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    convert h2 using 1
    funext c
    by_cases h : c = b
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]
  have hu : ∀ v ∈ Λ.La, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b := by
    intro v hv b
    obtain ⟨y, hy⟩ := (hU (Pi.single b (N : E))).1 (he b) v hv
    refine ⟨y, ?_⟩
    change algebraMap (𝓞 E) E y = _
    rw [hy, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Pi.single_eq_of_ne hc]
    · simp
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun b => b.elim0⟩
    obtain ⟨m, w, lam, hw⟩ := exists_dualFamily_of_nsmul_integral Λ.La hN hu
    let e : Fin n → Λ.La := fun b => ⟨Pi.single b (N : E), he b⟩
    have hx : ∀ i, ∃ x : Dw.La, ∑ j, lam i (e j) • a j = (N ^ 2) • x := by
      intro i
      refine h (Matrix.of fun _ j => (lam i (e j) : E) / N) ?_ (fun _ j => lam i (e j)) ?_ ⟨0, hn⟩
      · intro v hv
        rw [mem_stdLat_iff_integral]
        intro b
        refine ⟨lam i ⟨v, hv⟩, ?_⟩
        choose u hu' using hu v hv
        have h1 : ((N : 𝓞 E) * N) • (⟨v, hv⟩ : Λ.La) = ∑ j, u j • e j := by
          apply Subtype.ext
          funext c
          simp only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
          rw [Finset.sum_eq_single c]
          · simp only [Pi.single_eq_same, Algebra.smul_def]
            change _ = (u c : E) * _
            rw [hu']; simp; ring
          · intro d _ hd
            simp [Pi.single_eq_of_ne hd.symm]
          · simp
        have h2 := congrArg (fun z => ((lam i z : 𝓞 E) : E)) h1

        simp only [map_smul, map_sum, smul_eq_mul] at h2
        push_cast at h2
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        apply mul_left_cancel₀ (mul_ne_zero hN' hN')
        rw [Finset.mul_sum]
        refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
        have := hu' j
        change (u j : E) * (lam i (e j) : E) = _
        rw [this]; field_simp
      · intro _ j
        simp only [Matrix.of_apply]; field_simp
    choose x hx using hx
    choose v hv using fun i => hu (w i) (w i).2
    refine ⟨m, x, v, fun i => ⟨w i, (w i).2, hv i⟩, fun b => ?_⟩
    have := Dw.proj
    have hd : ∀ j, ∑ i, v i b * lam i (e j) = if j = b then (N : 𝓞 E) ^ 2 else 0 := by
      intro j
      apply inj
      have h1 := congrFun (congrArg Subtype.val (hw (e j))) b
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def] at h1
      have h2 : (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = (N : E) * (e j : Fin n → E) b := by
        rw [← h1, Finset.mul_sum]
        change algebraMap (𝓞 E) E _ = _

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        change (v i b : E) * _ = _
        rw [hv]; ring
      change (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = _
      rw [h2]
      by_cases hj : j = b
      · subst hj; simp [e, sq]
      · simp [e, hj]
    apply smul_right_injective Dw.La (pow_ne_zero 2 hNO)
    have hx' : ∀ i, ((N : 𝓞 E) ^ 2) • x i = ∑ j, lam i (e j) • a j := by
      intro i
      rw [hx, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
    calc ((N : 𝓞 E) ^ 2) • a b = ∑ j, (∑ i, v i b * lam i (e j)) • a j := by
          simp [hd]
      _ = ∑ i, v i b • ∑ j, lam i (e j) • a j := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = ((N : 𝓞 E) ^ 2) • ∑ i, v i b • x i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hx', smul_comm]
  · rintro ⟨m, x, v, hv, ha⟩ mu hmu cm hcm i
    choose w hw hvw using hv
    choose y hy using fun k => (mem_stdLat_iff_integral _).1 (hmu (w k) (hw k)) i
    have hd : ∀ k, ∑ j, cm i j * v k j = (N : 𝓞 E) ^ 2 * y k := by
      intro k
      apply inj
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _

      rw [map_sum, map_mul]
      change _ = _ * (y k : E)
      rw [hy]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      change (cm i j : E) * (v k j : E) = _
      rw [hcm, hvw]; simp; ring
    refine ⟨∑ k, y k • x k, ?_⟩
    calc ∑ j, cm i j • a j = ∑ k, (∑ j, cm i j * v k j) • x k := by
          simp only [ha, Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = _ := by
          rw [← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow, Finset.smul_sum]
          simp only [hd, mul_smul]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZhStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ)

theorem act_natCast (m : ℕ) : Xo.univ.t.act.act m = 𝟙 Xo.univ.t.G ^ m := by
  induction m with
  | zero =>
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, Xo.univ.t.act.add, ih, Xo.univ.t.act.one, pow_succ]

theorem comp_list_prod {T T' : Over Xo.X} (h : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map fun x => h ≫ x).prod = h ≫ L.prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, MonObj.comp_one]
  | cons x L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem inZh_comp {T T' : Over Xo.X} (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) :
    InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := comp_list_prod Xo h (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j))
    rw [ha.2 mu hmu cm hcm i, MonObj.comp_one, List.map_ofFn] at h1
    simpa only [Function.comp_def, Category.assoc] using h1

theorem inZh_mul {T : Over Xo.X} (a a' : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a)
    (ha' : InZh Xo Λ N a') : InZh Xo Λ N (fun b => a b * a' b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [mul_pow, ha.1 b, ha'.1 b, _root_.mul_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have h2 := ha'.2 mu hmu cm hcm i
    rw [List.prod_ofFn] at h1 h2 ⊢
    have h3 : ∀ j, (a j * a' j) ≫ Xo.univ.t.act.act (cm i j) =
        (a j ≫ Xo.univ.t.act.act (cm i j)) * (a' j ≫ Xo.univ.t.act.act (cm i j)) := fun j => by
      have := Xo.univ.t.act.hom (cm i j)
      exact MonObj.mul_comp _ _ _
    simp only [h3]
    rw [Finset.prod_mul_distrib, h1, h2, _root_.mul_one]

theorem geoInj_comp {S T : Type} [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X)
    (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hz : GeoInj Xo x0 z) :
    GeoInj Xo x1 (fun i b => h ≫ z i b) := by
  intro k _ χ g hg i j hij
  let g' : ptO Xo (spMap (χ.comp ψ) ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap (χ.comp ψ)) rfl
  have hc : spMap (χ.comp ψ) = g.left ≫ h.left := by
    rw [hg, hh]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine hz k (χ.comp ψ) g' rfl (funext fun b => Over.OverMorphism.ext ?_)
  have h1 := congrArg (fun f => f.left) (congrFun hij b)
  change spMap (χ.comp ψ) ≫ (z i b).left = spMap (χ.comp ψ) ≫ (z j b).left
  rw [hc]
  simpa only [Over.comp_left, Category.assoc] using h1

theorem inZh_of_killedBy (hΛ : Λ.TrivAt l.M) {T : Over Xo.X} (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) : InZh Xo Λ N u := by
  classical
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [pow_two, pow_mul, (hu b).1, one_pow]
  · obtain ⟨k, hk, -, hk2⟩ := hΛ
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨hN, e, he⟩ := hu j
    have hv : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.La := by
      refine hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_)
      intro b _
      by_cases hb : b = j
      · subst hb; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := Submodule.mem_one.1 (hmu _ hv i (Set.mem_univ i))
    have hm' : (m : E) = (k : E) * mu i j := by
      have : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = (k : E) • (Pi.single j (1 : E) : Fin n → E) := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hm
      exact hm
    have hcmk : cm i j * k = N * m := by
      apply RingOfIntegers.ext
      have h1 : ((cm i j * k : 𝓞 E) : E) = (cm i j : E) * (k : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      have h2 : ((N * m : 𝓞 E) : E) = (N : E) * (m : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      rw [h1, h2, hcm, hm']; ring
    have hM : (l.M : 𝓞 E) ∈ l.Mb := by
      have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf h1).1
    have hcop : IsCoprime (k : 𝓞 E) ((l.M : 𝓞 E) ^ e) := (Nat.Coprime.cast hk).pow_right
    obtain ⟨p, q, hpq⟩ := hcop
    have hsplit : cm i j = N * (m * p) + (cm i j * q) * (l.M : 𝓞 E) ^ e := by
      linear_combination (-cm i j) * hpq + p * hcmk
    have := Xo.univ.t.act.hom (m * p)
    show u j ≫ Xo.univ.t.act.act (cm i j) = 1
    rw [hsplit, Xo.univ.t.act.add, MonObj.comp_mul,
      he _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hM e)), _root_.mul_one, Xo.univ.t.act.mul,
      ← Category.assoc, act_natCast, MonObj.comp_pow, Category.comp_id, hN, MonObj.one_comp]

end GlobalTheory.ZhStable

namespace GlobalTheory

theorem inZh_geoInj_stable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) :=
  fun _ _ _ _ _ _ _ Xo _ Λ N =>
    ⟨fun _ _ h a => ZhStable.inZh_comp Xo Λ N h a, fun _ a a' => ZhStable.inZh_mul Xo Λ N a a',
      fun _ _ _ _ x0 x1 ψ h hh _ z => ZhStable.geoInj_comp Xo x0 x1 ψ h hh z,
      fun hΛ _ u => ZhStable.inZh_of_killedBy Xo Λ N hΛ u⟩

end GlobalTheory
end
