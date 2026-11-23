module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle002
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini :
    Euler → Fub → SideAbs := by
  intro hE hF V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K
    T _ _ _ _ _ _ _ _ Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hRP hRPT j ji jv
    hqj hpj hK μ μi m ν νi nv hP hPi hPv S a b ha hb hEa hEb θ θi θv hqθ hpθ cθi cθv
    δ z cz hpz hinv hC hB φi φ cφi sφi cφ hS
  classical
  have invI : ∀ t, (ji t)⁻¹ * q δ * θi (ji t) = q δ := by
    intro t
    obtain ⟨τ, h1, -⟩ := hRPT.surj t (fun _ => 1) (Filter.Eventually.of_forall fun v => one_mem _)
    have h := congrArg q (hinv τ)
    rw [map_mul, map_mul, map_inv, hqθ, hqj, h1] at h
    exact h
  have invV : ∀ v t, (jv v t)⁻¹ * p v δ * θv v (jv v t) = p v δ := by
    intro v t
    have hev : ∀ᶠ w in Filter.cofinite, Function.update (fun w => (1 : Tv w)) v t w ∈ KT w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
      exact one_mem _
    obtain ⟨τ, -, h1⟩ := hRPT.surj 1 _ hev
    have h2 : pT v τ = t := by rw [h1 v, Function.update_self]
    have h := congrArg (p v) (hinv τ)
    rw [map_mul, map_mul, map_inv, hpθ, hpj, h2] at h
    exact h
  have twI : ∀ t g, (ji t * g)⁻¹ * q δ * θi (ji t * g) = g⁻¹ * q δ * θi g := by
    intro t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (ji t)⁻¹ * q δ * (θi (ji t) * θi g)
        = g⁻¹ * ((ji t)⁻¹ * q δ * θi (ji t)) * θi g := by simp only [mul_assoc]
      _ = g⁻¹ * q δ * θi g := by rw [invI]
  have twV : ∀ v t g, (jv v t * g)⁻¹ * p v δ * θv v (jv v t * g) = g⁻¹ * p v δ * θv v g := by
    intro v t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (jv v t)⁻¹ * p v δ * (θv v (jv v t) * θv v g)
        = g⁻¹ * ((jv v t)⁻¹ * p v δ * θv v (jv v t)) * θv v g := by simp only [mul_assoc]
      _ = g⁻¹ * p v δ * θv v g := by rw [invV]
  let Fi : Gi → ℂ := fun x => ∫ s, φi (q (z s) * (x⁻¹ * q δ * θi x))
  let Fv : ∀ v, Gv v → ℂ := fun v x => φ v (x⁻¹ * p v δ * θv v x)
  have hf := hF Gi Ti μi ji νi hPi θi (q δ) (fun s => q (z s)) cθi (hRP.cq.comp cz) invI hC hB
    φi cφi sφi
  have hfm : Measurable Fi := hf.1
  have hf2 : qI μi ji νi Fi = ∫ s, qI μi ji νi fun x => φi (q (z s) * (x⁻¹ * q δ * θi x)) := hf.2
  have hFiI : ∀ t g, Fi (ji t * g) = Fi g := by
    intro t g
    show (∫ s, φi (q (z s) * ((ji t * g)⁻¹ * q δ * θi (ji t * g)))) = ∫ s, φi (q (z s) * (g⁻¹ * q δ * θi g))
    simp only [twI]
  have hFv : ∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g := by
    intro v
    refine ⟨((cφ v).comp ((continuous_inv.mul continuous_const).mul (cθv v))).measurable, ?_⟩
    intro t g
    show φ v ((jv v t * g)⁻¹ * p v δ * θv v (jv v t * g)) = φ v (g⁻¹ * p v δ * θv v g)
    rw [twV]
  have hFS : ∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧
      ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0) := by
    intro v hv x
    obtain ⟨h1, h2⟩ := hS v hv
    constructor
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 1
      rw [h1]
      exact Set.indicator_of_mem ((h2 x).2 h) _
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 0
      rw [h1]
      exact Set.indicator_of_notMem (fun hm => h ((h2 x).1 hm)) _
  have he := hE V G Gi Gv q p K T Ti Tv qT pT KT hRP hRPT j ji jv hqj hpj hK μ μi m ν νi nv
    hP hPi hPv S a b ha hb hEa hEb Fi Fv hfm hFiI hFv hFS
  have key : (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) *
      ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) = fun x => Fi (q x) * ∏ᶠ v, Fv v (p v x) := by
    funext x
    have h1 : ∀ s, q (z s * (x⁻¹ * δ * θ x)) = q (z s) * ((q x)⁻¹ * q δ * θi (q x)) := by
      intro s
      rw [map_mul, map_mul, map_mul, map_inv, hqθ]
    have h2 : ∀ s v, p v (z s * (x⁻¹ * δ * θ x)) = (p v x)⁻¹ * p v δ * θv v (p v x) := by
      intro s v
      rw [map_mul, hpz, one_mul, map_mul, map_mul, map_inv, hpθ]
    simp only [h1, h2]
    exact integral_mul_const _ _
  rw [key]
  exact ⟨he.1, he.2.trans (congrArg (fun w => ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * w *
    ∏ v ∈ S, qI (m v) (jv v) (nv v) (Fv v)) hf2)⟩
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem coord_comm {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (φ : R →ₗ[F] F) (s : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s) :
    Commute (s.map φ) γ := by
  have hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x := by
    intro r x
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r := by
    intro r x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  show s.map φ * γ = γ * s.map φ
  ext a c
  have h := congrArg φ (congrFun (congrFun hs a) c)

  simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr] using h

private theorem coord_sum {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (b : Module.Basis ι F R) (B : Finset ι) (s : Matrix (Fin n) (Fin n) R)
    (hB : ∀ a c, (b.repr (s a c)).support ⊆ B) :
    s = ∑ i ∈ B, b i • (s.map (b.coord i)).map (algebraMap F R) := by
  ext a c
  rw [Matrix.sum_apply]
  conv_lhs => rw [← b.linearCombination_repr (s a c)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

private theorem sum_comm_of {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (e : ι → R) (B : Finset ι) (S T : ι → Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, S i * T j = T j * S i) :
    (∑ i ∈ B, e i • (S i).map (algebraMap F R)) * (∑ j ∈ B, e j • (T j).map (algebraMap F R)) =
      (∑ j ∈ B, e j • (T j).map (algebraMap F R)) * (∑ i ∈ B, e i • (S i).map (algebraMap F R)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem comm_alg {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (hγ : γ.charpoly.Separable) (s t : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s)
    (ht : t * γ.map (algebraMap F R) = γ.map (algebraMap F R) * t) : s * t = t * s := by
  classical
  let b := Module.Basis.ofVectorSpace F R
  let B := Finset.univ.biUnion fun a => Finset.univ.biUnion fun c =>
    (b.repr (s a c)).support ∪ (b.repr (t a c)).support
  have hsB : ∀ a c, (b.repr (s a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_left _ hi⟩⟩
  have htB : ∀ a c, (b.repr (t a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_right _ hi⟩⟩
  have h := sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i))
    (fun i => t.map (b.coord i)) fun i j =>
      (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq
  rwa [← coord_sum b B s hsB, ← coord_sum b B t htB] at h

theorem UpperTheory.centralizer_commutative_of_separable_charpoly :
    CentComm := by
  intro F R _ _ _ f n γ hγ s t hs ht
  letI : Algebra F R := f.toAlgebra
  exact comm_alg γ hγ s t hs ht
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory Pointwise in
theorem UpperTheory.orbital_integral_fubini :
    Fub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP θ δ z hθ hz hinv hC hB φ hφ hφc
  haveI : μ.IsHaarMeasure := hP.1.1
  obtain ⟨ρ, hρc, hρn, hρD⟩ := normEx G T μ j ν hP
  have hw : Continuous fun x : G => x⁻¹ * δ * θ x :=
    (continuous_inv.mul continuous_const).mul hθ
  have hFm : Measurable (Function.uncurry fun (s : ℝ) (x : G) => φ (z s * (x⁻¹ * δ * θ x))) :=
    (hφ.comp ((hz.comp continuous_fst).mul (hw.comp continuous_snd))).measurable
  have hwi : ∀ (t : T) (g : G), (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * δ * θ g := by
    intro t g
    have h := hinv t
    calc (j t * g)⁻¹ * δ * θ (j t * g) = g⁻¹ * ((j t)⁻¹ * δ * θ (j t)) * θ g := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = g⁻¹ * δ * θ g := by rw [h]
  have hFi : ∀ (s : ℝ) (t : T) (g : G),
      φ (z s * ((j t * g)⁻¹ * δ * θ (j t * g))) = φ (z s * (g⁻¹ * δ * θ g)) := by
    intro s t g
    rw [hwi]
  obtain ⟨B, hBc, hBm⟩ := hB (tsupport φ) hφc
  have hEc : IsCompact ((fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ)) :=
    (hBc.prod hφc).image ((hz.comp continuous_fst).inv.mul continuous_snd)
  obtain ⟨C, hCc, hCm⟩ := hC _ hEc
  obtain ⟨D, hDc, hDm⟩ := hρD C hCc
  have hsupp : ∀ (s : ℝ) (x : G), φ (z s * (x⁻¹ * δ * θ x)) ≠ 0 →
      s ∈ B ∧ x ∈ Set.range j * C := by
    intro s x h
    have hm : z s * (x⁻¹ * δ * θ x) ∈ tsupport φ := subset_tsupport φ (Function.mem_support.2 h)
    have hs := hBm s x hm
    have he : x⁻¹ * δ * θ x ∈ (fun p : ℝ × G => (z p.1)⁻¹ * p.2) '' (B ×ˢ tsupport φ) :=
      ⟨(s, z s * (x⁻¹ * δ * θ x)), ⟨hs, hm⟩, by simp⟩
    obtain ⟨t, y, hy, hx⟩ := hCm x he
    exact ⟨hs, Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, y, hy, hx.symm⟩⟩
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  obtain ⟨R, hR⟩ := hDc.exists_bound_of_continuousOn (f := fun x => ((ρ x : NNReal) : ℝ))
    (NNReal.continuous_coe.comp hρc).continuousOn
  have hpt : ∀ (s : ℝ) (x : G), ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ≤
      D.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R) x := by
    intro s x
    by_cases h0 : φ (z s * (x⁻¹ * δ * θ x)) = 0
    · simp [h0]
    by_cases h1 : ρ x = 0
    · simp [h1]
    have hx : x ∈ D := hDm x (hsupp s x h0).2 h1
    rw [Set.indicator_of_mem hx]
    refine mul_le_mul' ?_ ?_
    · rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)
    · rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hR x hx))
  have hin : ∀ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≤
      B.indicator (fun _ => ENNReal.ofReal M * ENNReal.ofReal R * μ D) s := by
    intro s
    by_cases hs : s ∈ B
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator_const hDc.measurableSet]
      exact lintegral_mono fun x => hpt s x
    · have h0 : ∀ x : G, φ (z s * (x⁻¹ * δ * θ x)) = 0 := fun x => by
        by_contra h
        exact hs (hsupp s x h).1
      simp [h0]
  have hfin : ∫⁻ s : ℝ, ∫⁻ x, ‖φ (z s * (x⁻¹ * δ * θ x))‖ₑ * (ρ x : ENNReal) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hin)
    rw [lintegral_indicator_const hBc.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hDc.measure_lt_top.ne)
      hBc.measure_lt_top.ne
  obtain ⟨h1, h2⟩ := quotFub_of normEx quotEq G T μ j ν hP ℝ volume
    (fun s x => φ (z s * (x⁻¹ * δ * θ x))) hFm hFi (fun x => (ρ x : ENNReal)) hρn hfin
  exact ⟨h1.1, h2⟩
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology
open scoped ENNReal

private theorem uni_map {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [MeasurableSpace A] [BorelSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [MeasurableSpace B] [BorelSpace B] {m : Measure A} (h : Uni m) (e : A ≃ₜ* B) :
    Uni (m.map e) := by
  obtain ⟨h1, h2⟩ := h
  have he : Measurable e := (map_continuous e).measurable
  refine ⟨e.isHaarMeasure_map m, ⟨?_⟩⟩
  rw [Measure.inv_def, Measure.map_map measurable_inv he]
  have hc : (Inv.inv ∘ e : A → B) = e ∘ Inv.inv := by
    funext x
    simp
  rw [hc, ← Measure.map_map he measurable_inv, Measure.map_inv_eq_self]

private theorem qI_one_id {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R]
    [BorelSpace R] {l : Measure R} (hP : Pair l (MonoidHom.id R) l) :
    qI l (MonoidHom.id R) l (fun _ => 1) = 1 := by
  obtain ⟨ρ, -, hρ, -⟩ := normEx R R l (MonoidHom.id R) l hP
  obtain ⟨-, -, h3⟩ := quotEq R R l (MonoidHom.id R) l hP (fun _ => 1) measurable_const
    (fun _ _ => rfl) _ hρ
  rw [h3]
  have h := hρ.2 1
  simp only [MonoidHom.id_apply, mul_one] at h
  simp only [one_mul]
  have h4 : ∫ x, (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ) ∂l = ((∫ x, (ρ x : ℝ≥0∞).toReal ∂l : ℝ) : ℂ) :=
    integral_ofReal
  rw [h4, integral_toReal hρ.1.aemeasurable (ae_of_all _ fun x => ENNReal.coe_lt_top), h]
  simp

theorem UpperTheory.quotient_measure_split :
    SplitQ := by
  intro G₁ _ _ _ _ _ _ _ _ T₁ _ _ _ _ _ _ _ _ R _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _
    T _ _ _ _ _ _ _ _ μ j₁ ν l hP hl e eT j hj
  have hPl : Pair l (MonoidHom.id R) l := ⟨hl, IsClosedEmbedding.id, hl⟩
  obtain ⟨hPP, hQ⟩ := quotProd_of normEx quotEq G₁ T₁ R R μ j₁ ν hP l (MonoidHom.id R) l hPl
  have hje : ∀ x : T₁ × R, j (eT x) = e (j₁.prodMap (MonoidHom.id R) x) := fun x => hj x
  have hcomp : (j : T → G) = e ∘ (j₁.prodMap (MonoidHom.id R)) ∘ eT.symm := by
    funext t
    have := hje (eT.symm t)
    simpa using this
  have hcl : IsClosedEmbedding j := by
    rw [hcomp]
    exact e.toHomeomorph.isClosedEmbedding.comp
      (hPP.2.1.comp eT.symm.toHomeomorph.isClosedEmbedding)
  have hPair : Pair ((μ.prod l).map e) j ((ν.prod l).map eT) :=
    ⟨uni_map hPP.1 e, hcl, uni_map hPP.2.2 eT⟩
  refine ⟨hPair, fun F hF hFi => ?_⟩
  have he : Measurable e := (map_continuous e).measurable
  have heT : Measurable eT := (map_continuous eT).measurable
  have hjm : Measurable j := hcl.continuous.measurable
  have hjp : Measurable (j₁.prodMap (MonoidHom.id R)) := hPP.2.1.continuous.measurable
  have hf : Measurable (fun x => F (e (x, (1 : R)))) :=
    hF.comp (he.comp (measurable_id.prodMk measurable_const))
  have hfi : ∀ t g, F (e (j₁ t * g, (1 : R))) = F (e (g, (1 : R))) := by
    intro t g
    have h : e (j₁ t * g, (1 : R)) = j (eT (t, 1)) * e (g, 1) := by
      rw [hj, ← map_mul]
      simp
    rw [h, hFi]
  have h1 := (hQ (fun x => F (e (x, (1 : R)))) (fun _ => 1) hf hfi measurable_const
    (fun _ _ => rfl)).2
  rw [qI_one_id hPl, mul_one] at h1
  rw [← h1]
  have hmap : (ν.prod l).map (fun t => e (j₁.prodMap (MonoidHom.id R) t)) =
      ((ν.prod l).map eT).map j := by
    rw [Measure.map_map hjm heT]
    congr 1
    funext t
    exact (hje t).symm
  have h2 := (quotMap_of normEx quotEq (G₁ × R) (T₁ × R) G T (μ.prod l)
    (j₁.prodMap (MonoidHom.id R)) (ν.prod l) hPP ((μ.prod l).map e) j ((ν.prod l).map eT) hPair
    e 1 rfl hmap F hF hFi).2
  rw [← h2]
  congr 1
  funext g
  have h3 : e g = j (eT (1, g.2)) * e (g.1, 1) := by
    rw [hj, ← map_mul]
    simp
  simp only [mul_one]
  rw [h3, hFi]
end

section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal

theorem UpperTheory.quotient_haar_measure_pushforward :
    QPush := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν μ' j' ν' hP hP' U hU π πT hπ hπT hc hμ hν F F' hF hFi hF' hF'i hs hFF
  have hjc : Continuous j := hP.2.1.continuous
  have hUT : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hjc
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hUT.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : BorelSpace U := Subtype.borelSpace (fun x => x ∈ (U : Set G))
  haveI : BorelSpace (U.comap j) := Subtype.borelSpace (fun x => x ∈ ((U.comap j : Subgroup T) : Set T))
  let i : U.comap j →* U := (j.comp (U.comap j).subtype).codRestrict U (fun t => t.2)
  have hi : ∀ t : U.comap j, (i t : G) = j t := fun _ => rfl
  obtain ⟨hPU, hO⟩ := quotOpen_of normEx quotEq G T μ j ν hP U hU i hi
  obtain ⟨ρ', hρc, hρ, -⟩ := normEx H T' μ' j' ν' hP'
  have embG : MeasurableEmbedding (fun u : U => (u : G)) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have embT : MeasurableEmbedding (fun t : U.comap j => (t : T)) :=
    MeasurableEmbedding.subtype_coe hUT.measurableSet
  have mapG : (μ.comap fun u : U => (u : G)).map (fun u : U => (u : G)) = μ.restrict (U : Set G) := by
    rw [embG.map_comap]; congr 1; exact Subtype.range_coe
  have mapT : (ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T)) =
      ν.restrict (j ⁻¹' (U : Set G)) := by
    rw [embT.map_comap]; congr 1; exact Subtype.range_coe
  have hρm : Measurable fun h : H => ((ρ' h : NNReal) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hρc.measurable
  have hn : IsNrm i (ν.comap fun t : U.comap j => (t : T)) (fun u : U => ((ρ' (π u) : NNReal) : ℝ≥0∞)) := by
    refine ⟨hρm.comp (hπ.measurable.comp measurable_subtype_coe), fun x => ?_⟩
    have hg : Measurable fun s : T' => ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) :=
      hρm.comp ((hP'.2.1.continuous.measurable).mul_const _)
    calc ∫⁻ t, ((ρ' (π ((i t * x : U) : G)) : NNReal) : ℝ≥0∞) ∂(ν.comap fun t : U.comap j => (t : T))
        = ∫⁻ t, (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)) ((fun t : U.comap j => (t : T)) t)
            ∂(ν.comap fun t : U.comap j => (t : T)) := by
          refine lintegral_congr fun t => ?_
          simp only [Subgroup.coe_mul, map_mul, hi, hc]
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)
            ∂((ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T))) :=
          (embT.lintegral_map (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞))).symm
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞) ∂(ν.restrict (j ⁻¹' (U : Set G))) := by
          rw [mapT]
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂((ν.restrict (j ⁻¹' (U : Set G))).map πT) :=
          (lintegral_map hg hπT.measurable).symm
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂ν' := by rw [hν]
      _ = 1 := hρ.2 (π x)
  have hFU : Measurable fun u : U => F u := hF.comp measurable_subtype_coe
  have hFUi : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    rw [Subgroup.coe_mul, hi, hFi]
  have hgm : Measurable fun h : H => F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) :=
    hF'.mul (Complex.measurable_ofReal.comp hρm.ennreal_toReal)
  have e1 := (hO F hF hFi hs).2
  have e2 := (quotEq (↥U) (↥(U.comap j)) (μ.comap fun u : U => (u : G)) i
    (ν.comap fun t : U.comap j => (t : T)) hPU (fun u : U => F u) hFU hFUi _ hn).2.2
  have e3 := (quotEq H T' μ' j' ν' hP' F' hF' hF'i _ hρ).2.2
  rw [e1, e2, e3]
  calc ∫ u : U, F u * ((((ρ' (π u) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.comap fun u : U => (u : G))
      = ∫ u : U, (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))
            ((fun u : U => (u : G)) u) ∂(μ.comap fun u : U => (u : G)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hFF u u.2]
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)
          ∂((μ.comap fun u : U => (u : G)).map (fun u : U => (u : G))) :=
        (embG.integral_map (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))).symm
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.restrict (U : Set G)) := by
        rw [mapG]
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂((μ.restrict (U : Set G)).map π) :=
        (integral_map hπ.aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂μ' := by rw [hμ]
end
