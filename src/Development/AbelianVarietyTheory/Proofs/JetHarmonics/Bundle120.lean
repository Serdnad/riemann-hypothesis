module

public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScaledSpan

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def sc (s : R) (N : Submodule R A) : Submodule R A := N.map (s • LinearMap.id)

theorem mem_sc {s : R} {N : Submodule R A} {x : A} : x ∈ sc s N ↔ ∃ y ∈ N, x = s • y := by
  simp [sc, eq_comm]

theorem sc_mul_le {s t : R} {M M' N N' : Submodule R A} (h : M ≤ sc s M') (h' : N ≤ sc t N') :
    M * N ≤ sc (s * t) (M' * N') := by
  refine Submodule.mul_le.2 fun m hm n hn => ?_
  obtain ⟨a, ha, rfl⟩ := mem_sc.1 (h hm)
  obtain ⟨b, hb, rfl⟩ := mem_sc.1 (h' hn)
  exact mem_sc.2 ⟨a * b, Submodule.mul_mem_mul ha hb, smul_mul_smul_comm s a t b⟩

theorem sc_pow_le {s : R} {M M' : Submodule R A} (h : M ≤ sc s M') (n : ℕ) :
    M ^ n ≤ sc (s ^ n) (M' ^ n) := by
  induction n with
  | zero => intro x hx; exact mem_sc.2 ⟨x, by simpa using hx, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ, pow_succ]; exact sc_mul_le ih h

theorem sc_le_of_dvd {s t : R} {M N : Submodule R A} (hd : t ∣ s) (h : M ≤ N) : sc s M ≤ sc t N := by
  obtain ⟨c, rfl⟩ := hd
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_sc.1 hx
  exact mem_sc.2 ⟨c • y, N.smul_mem c (h hy), mul_smul t c y⟩

end General

variable {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem emb_WWc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.WWc s w) ≤ sc s (X.emb w (X.thAll w)) := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, by simp⟩

theorem emb_Thc_le (X : WeightAlgebra.PJ D B P6 j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) :
    X.emb w (X.Thc s w) ≤
      sc (s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n)) (X.emb w (X.shortTh w)) := by
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  refine mem_sc.2 ⟨_, ⟨y, hy, rfl⟩, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

theorem nnW_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {ka wL wF : WeightFamilies.Wt D j} {T n : ℕ} (h : WeightAlgebra.IsF' ka wL wF T n) :
    nnW B hinj EX ka = nnW B hinj EX wL ^ T * nnW B hinj EX wF := by
  obtain ⟨-, hP, hM⟩ := h
  have hP' : ∀ τ i, ka.aP τ i = wL.aP τ i * T + wF.aP τ i := fun τ i => by
    have := hP τ i
    zify
    linarith
  have hM' : ∀ τ i, ka.aM τ i = wL.aM τ i * T + wF.aM τ i := fun τ i => by
    have := hM τ i
    zify
    linarith
  have h1 : Dplus ka = Dplus wL * T + Dplus wF := by
    simp only [Dplus, hP', Finset.sum_add_distrib, Finset.sum_mul]
  have h2 : Dminus ka = Dminus wL * T + Dminus wF := by
    simp only [Dminus, hM', Finset.sum_add_distrib, Finset.sum_mul]
  simp only [nnW, h1, h2, Fin.prod_univ_two]
  ring

theorem nnW_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) : nnW B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact_mod_cast (D.host.g_prime i).ne_zero
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))

theorem theta_le_sigma_smul : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  intro D B P6 j X hinj EX p ka wL wF T hF hn hT
  refine ⟨?_, fun F hF' => mem_sc.1 (?_ : F ∈ sc _ _)⟩
  · refine mul_ne_zero (nnW_ne_zero B hinj EX ka) (Nat.cast_ne_zero.2 ?_)
    have hq : D.host.q ≠ 0 := (D.host.hyp.1 : D.host.q.Prime).ne_zero
    have hd : D.host.d ≠ 0 := (D.host.hyp.2.1 : D.host.d.Prime).ne_zero
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    have hS : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    unfold pPow
    positivity
  · revert F
    change X.Theta _ ka wL wF T ≤ _
    have hnn := nnW_eq B hinj EX hF
    refine sup_le (sup_le ?_ ?_) ?_
    · refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) T) (emb_Thc_le X _ wF)).trans
        (sc_le_of_dvd ⟨(zOwnP D p wF : 𝓞 B.KO), ?_⟩ (le_sup_left.trans le_sup_left))
      simp only [scalOfP, sigRec, hnn, pPow]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
      refine (sc_mul_le (sc_pow_le (emb_WWc_le X _ wL) _) (emb_Thc_le X _ _)).trans
        (sc_le_of_dvd ⟨(zOwnP D p (X.wF0 wL wF) : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (WeightFamilies.dimY D j * wL.n)), ?_⟩
          (le_sup_right.trans le_sup_left))
      have e : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
      simp only [scalOfP, sigRec, hnn, pPow, e, Nat.add_sub_cancel_left]
      unfold WeightAlgebra.PJ.wF0
      push_cast
      ring
    · refine (emb_Thc_le X _ ka).trans
        (sc_le_of_dvd ⟨(zOwnP D p ka : 𝓞 B.KO) *
          ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * (T * wL.n)), ?_⟩ le_sup_right)
      simp only [scalOfP, sigRec, hnn, pPow, hn]
      push_cast
      ring

end GlobalTheory.ScaledSpan
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {C : Type} [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}


omit [NumberField K] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] in
theorem coord_one_tmul_smul (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (r : F) (f : C) :
    z.symm (1 ⊗ₜ[F] (r • f)) = algebraMap F K r • z.symm (1 ⊗ₜ[F] f) := by
  rw [← map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, smul_eq_mul]

theorem spanK_span (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (s : Set C) :
    spanK z (Submodule.span (𝓞 F) s : Set C) = spanK z s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hi : IsIntegral ℤ (algebraMap F K (r : F)) :=
        (RingOfIntegers.isIntegral_coe r).map (algebraMap F K).toIntAlgHom
      have e : z.symm (1 ⊗ₜ[F] (r • x)) = (⟨algebraMap F K (r : F), hi⟩ : 𝓞 K) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F r x, coord_one_tmul_smul]
        rfl
      simp only [e]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem spanK_isLatIn (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (hfg : M.FG)
    (htop : Submodule.span F (M : Set C) = ⊤) : Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (spanK z (M : Set C)) := by
  constructor
  · obtain ⟨s, rfl⟩ := hfg
    rw [spanK_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z (M : Set C) : Set (Fin n → K)) := by
      intro f
      have hf : f ∈ Submodule.span F (M : Set C) := htop ▸ Submodule.mem_top
      induction hf using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [TensorProduct.tmul_add, map_add (f := _)]
        exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        rw [coord_one_tmul_smul]
        exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := z.symm.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k f =>
      have e : (k ⊗ₜ[F] f : K ⊗[F] C) = k • (1 ⊗ₜ[F] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact Submodule.smul_mem _ _ (h1 f)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem supLattice_isLatIn_stable : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ g, ∀ F ∈ B.Mlat j ka, act g F ∈ B.Mlat j ka) → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Ms i) ∧ ∀ g : P, (O.Ms i).map ((O.ρ i g).restrictScalars (𝓞 K)) ≤ O.Ms i := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act h hL hact
  rw [h.Ms_eq]
  refine ⟨spanK_isLatIn z _ hL.toIsLattice.fg hL.span_eq_top, fun g => ?_⟩
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  show O.ρ i g (z.symm (1 ⊗ₜ f)) ∈ spanK z _
  rw [h.rho_eq]
  exact Submodule.subset_span ⟨act g f, hact g f hf, rfl⟩

end GlobalTheory.FormTies
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem pow_mul_short_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (ka wL : WeightFamilies.Wt D j) (hka : ka.n = D.R.nV)
    (step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      X.emb wL (X.thAll wL) * X.emb w (X.shortTh w) ≤ X.emb (WeightAlgebra.wadd w wL) (X.shortTh (WeightAlgebra.wadd w wL))) :
    ∀ (t : ℕ) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → deg w + t • deg wL = deg ka →
      X.emb wL (X.thAll wL) ^ t * X.emb w (X.shortTh w) ≤ X.emb ka (X.shortTh ka) := by
  intro t
  induction t with
  | zero =>
    intro w _ e
    rw [zero_smul, add_zero] at e
    obtain rfl := deg_inj e
    rw [pow_zero, one_mul]
  | succ t ih =>
    intro w hr e
    have hn : w.n + (t + 1) * wL.n = ka.n := congrArg (fun x : Deg D j => x.2.2) e
    rw [pow_succ, mul_assoc]
    refine le_trans (mul_le_mul' le_rfl (step w hr fun h0 => ?_)) (ih (WeightAlgebra.wadd w wL) (hr.trans (Nat.le_add_right _ _)) ?_)
    · have h1 : (t + 1) * wL.n = 0 := by omega
      exact (Nat.mul_eq_zero.1 h1).resolve_left (Nat.succ_ne_zero t)
    · rw [deg_wadd, ← e, succ_nsmul]
      abel

theorem emb_mul_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    {w w' w'' : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {N' : Submodule (𝓞 B.KO) (B.Cusp j w')}
    {N'' : Submodule (𝓞 B.KO) (B.Cusp j w'')}
    (h : ∀ G ∈ N', ∀ F ∈ N, ∃ H ∈ N'', X.inc w'' H = X.inc w' G * X.inc w F) :
    X.emb w N * X.emb w' N' ≤ X.emb w'' N'' := by
  rw [mul_comm, Submodule.mul_le]
  rintro _ ⟨G, hG, rfl⟩ _ ⟨F, hF, rfl⟩
  exact h G hG F hF

theorem mul_mem_span_of_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {s t : Set R} {N : Submodule O R}
    (h : ∀ g ∈ s, ∀ f ∈ t, g * f ∈ N) {x y : R} (hx : x ∈ Submodule.span O s) (hy : y ∈ Submodule.span O t) :
    x * y ∈ N := by
  have hle : Submodule.span O s * Submodule.span O t ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨g, hg, f, hf, rfl⟩
    exact h g hg f hf
  exact hle (Submodule.mul_mem_mul hx hy)

theorem productsShort_of_oneFactor (one : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL))) : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn := by
  intro hC D T h j hj hsh hone hA ka wL wF Tn hF hn hD hr hka
  have step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      (recPJ h j hj).emb wL ((recPJ h j hj).thAll wL) * (recPJ h j hj).emb w ((recPJ h j hj).shortTh w) ≤
        (recPJ h j hj).emb (WeightAlgebra.wadd w wL) ((recPJ h j hj).shortTh (WeightAlgebra.wadd w wL)) := by
    intro w hw h0
    refine emb_mul_le (recPJ h j hj) fun G hG F hF' => ?_
    have hc : (G.1 : T.R j) * F.1 ∈ cutR T.C j (WeightAlgebra.wadd w wL) := by
      rw [cutR_eq T.C hj]
      exact h.toLawsCore.mul j hj w wL _ (cutR_le T.C j w G.2) _ (cutR_le T.C j wL F.2)
    refine ⟨⟨_, hc⟩, ?_, ?_⟩
    · exact mul_mem_span_of_gen (one hC D T h j hj hsh hone hA w wL hw h0) hG hF'
    · exact (incG_mul deg (cutR T.C j) (deg_wadd w wL) G F _).symm
  have key := pow_mul_short_le (recPJ h j hj) ka wL hka step
  have hdeg : deg wF + Tn • deg wL = deg ka := by
    obtain ⟨_, hP, hM⟩ := hF
    refine Prod.ext (funext fun τ => funext fun i => ?_) (Prod.ext (funext fun τ => funext fun i => ?_) hn.symm)
    · change wF.aP τ i + Tn * wL.aP τ i = ka.aP τ i
      have := hP τ i
      zify
      linarith
    · change wF.aM τ i + Tn * wL.aM τ i = ka.aM τ i
      have := hM τ i
      zify
      linarith
  refine sup_le (sup_le (key Tn wF hr hdeg) (key _ _ (hr.trans (Nat.le_add_right _ _)) ?_)) le_rfl
  have e : deg ((recPJ h j hj).wF0 wL wF) = deg wF + WeightFamilies.dimY D j • deg wL := rfl
  rw [e, add_assoc, ← add_nsmul, Nat.add_sub_of_le hD, hdeg]

end GlobalTheory.FormTies
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C]
  [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_fg_of_subset [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] (N : Submodule (𝓞 F) C) (hN : N.FG)
    (s : Set C) (hs : s ⊆ N) : (spanK z s).FG := by
  classical
  obtain ⟨t, ht⟩ := hN
  have hle : spanK z s ≤ spanK z (t : Set C) := by
    unfold spanK
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span (𝓞 F) (t : Set C) := ht ▸ hs hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : z.symm (1 ⊗ₜ[F] (a • x)) =
          (RingOfIntegers.mapRingHom (algebraMap F K) a) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F a x, TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul,
          ← algebraMap_smul K (RingOfIntegers.mapRingHom (algebraMap F K) a)]
        rfl
      beta_reduce
      rw [e]
      exact Submodule.smul_mem _ _ hx
  have hfg : (spanK z (t : Set C)).FG := Submodule.fg_span (t.finite_toSet.image _)
  exact hfg.of_le hle

theorem span_spanK_eq_top (s : Set C) (hs : Submodule.span F s = ⊤) :
    Submodule.span K (spanK z s : Set (Fin n → K)) = ⊤ := by
  have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z s : Set (Fin n → K)) := by
    intro f
    have hf : f ∈ Submodule.span F s := hs ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (h1 f)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem scalOfP_sK_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {j : ℕ} (p : ℕ) (hp : 0 < p) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
  have h1 := fun w => (GlobalTheory.log_norm_normaliser D B hinj EX j w σ).1
  have h2 := fun a b c => ((GlobalTheory.RunIn.pPow_size D j ka).2.2.2.2.2 a b c).1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (h1 _))) (h1 _)) ?_
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  · exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h2 _ _ _))

theorem theta_spans_isLatIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v i) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act ht hp hF hn hD hM hSp h2
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  refine ⟨⟨?_, ?_⟩, ht.ThK_fg, ?_⟩
  · rw [ht.Th_eq]
    refine spanK_fg_of_subset z (B.Mlat j ka) hM.fg _ fun f hf => ?_
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 (hle hf)
    exact X.inc_inj ka e ▸ hg
  · rw [ht.Th_eq]
    apply span_spanK_eq_top
    apply top_unique
    rw [← hSp]
    apply Submodule.span_le.2
    intro f hf
    let a : 𝓞 B.KO := (scalOfP B hinj EX p ka wL wF T).sK
    let b : 𝓞 B.KO := ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n)
    have ha : (a : B.KO) ≠ 0 := by
      exact_mod_cast scalOfP_sK_ne_zero B hinj EX p hp ka wL wF T
    have hb : (b : B.KO) ≠ 0 := by
      dsimp [b]
      exact_mod_cast pow_ne_zero (D.R.f * D.R.r * ka.n) (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hm : X.inc ka (a • (b • f)) ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T := by
      apply (le_sup_right : X.emb ka (X.Thc a ka) ≤ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T)
      apply Submodule.mem_map.2
      refine ⟨a • (b • f), ?_, rfl⟩
      exact Submodule.mem_map.2 ⟨b • f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, rfl⟩
    have hs := Submodule.subset_span (R := B.KO) (s := {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}) hm
    have he : a • (b • f) = ((a : B.KO) * (b : B.KO)) • f := by
      rw [← algebraMap_smul B.KO a (b • f), ← algebraMap_smul B.KO b f, smul_smul]
    rw [he] at hs
    have := (Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}).smul_mem (((a : B.KO) * (b : B.KO))⁻¹) hs
    change f ∈ Submodule.span B.KO {F | X.inc ka F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T}
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero ha hb), one_smul] using this
  · apply top_unique
    have hs : Submodule.span K (spanK z (X.shortTh ka : Set _) : Set (Fin (O.nZ i) → K)) = ⊤ := span_spanK_eq_top z _ hSp
    rw [← hs]
    apply Submodule.span_mono
    intro x hx
    apply ht.ThK_ge
    exact spanK_mono z (fun f hf => by
      change X.inc ka f ∈ thetaPlain X ka wL wF T
      apply (le_sup_right : X.emb ka (X.shortTh ka) ≤ thetaPlain X ka wL wF T)
      exact Submodule.mem_map.2 ⟨f, hf, rfl⟩) hx
end GlobalTheory.FormTies
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ dd : ℝ, (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → ∀ v ∈ R.TK, ∀ ξ : Wp, (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re ∧ 0 < dd ∧ ∀ w ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v ξ) = ENNReal.ofReal (‖w‖ ^ 2 * (⟪ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v ξ⟫_ℂ).re / dd) := by
  first | exact @GlobalTheory.BesselNorm.norm_identity | exact GlobalTheory.BesselNorm.norm_identity | (intros; apply GlobalTheory.BesselNorm.norm_identity <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tensor_moment_transfer : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  first | exact @GlobalTheory.BesselPairing.pairing | exact GlobalTheory.BesselPairing.pairing | (intros; apply GlobalTheory.BesselPairing.pairing <;> assumption)
end
