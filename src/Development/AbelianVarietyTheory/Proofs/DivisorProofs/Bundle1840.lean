module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1808
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMoveDefiniteSimilitudePairMarked
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.ZDecay

theorem eq_zero_of_le_div {x K T : ℝ} (hx : 0 ≤ x) (h : ∀ t : ℝ, T ≤ t → 0 ≤ t → x * (1 + t) ≤ K) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have h1 := h (max (max T 0) (K / x)) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have h2 : K / x ≤ max (max T 0) (K / x) := le_max_right _ _
  have h3 : x * (K / x) = K := mul_div_cancel₀ _ hne
  nlinarith

theorem holFn_eq_zero {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    {w : ι → Fin n → ℤ} (hx : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {e : ι → Fin n → ℂ}
    (he : ∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f)
    (hinv : ∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, m * u ∈ UG Hm ∧ f (m * u) = f u)
    (hdec : ∀ k : ℕ, ∃ K : ℝ, ∀ u ∈ UG Hm, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((u τ)⁻¹.mulVec (e τ)) i‖ ≤ δ) →
      ‖f u‖ ≤ K * δ ^ k) :
    ∀ u ∈ UG Hm, f u = 0 := by
  intro u hu
  obtain ⟨P, hP, hfP⟩ := hf
  have hflow := GlobalTheory.HolDict.flowInv n ι Hm q x₀ w hx P e he hP (fun m hm v hv => by
    obtain ⟨h1, h2⟩ := hinv m hm v hv
    rw [hfP _ h1, hfP _ hv] at h2
    exact h2) u hu
  choose C A hCA using fun τ => GlobalTheory.HolDict.FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hx τ) (w τ) (e τ) (he τ) (u τ) (hu τ)
  have hC0 : ∀ τ, 0 ≤ C τ := fun τ => by
    obtain ⟨u', -, b, -, -, h, -⟩ := hCA τ 0 le_rfl
    have := (norm_nonneg _).trans h
    simpa using this
  obtain ⟨K, hK⟩ := hdec (2 * (∑ τ, A τ + 1))
  obtain ⟨-, -, hst, hbase⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ hx
  set C' : ℝ := ∑ τ, C τ + 1 with hC'
  have hCs : 0 ≤ ∑ τ, C τ := Finset.sum_nonneg fun τ _ => hC0 τ
  have hC'pos : 0 < C' := by linarith
  have hCle : ∀ τ, C τ ≤ C' := fun τ => by
    have := Finset.single_le_sum (f := C) (fun τ _ => hC0 τ) (Finset.mem_univ τ)
    linarith
  rw [← norm_eq_zero]
  refine eq_zero_of_le_div (K := (∏ τ, C τ) * K * C' ^ (∑ τ, A τ + 1)) (T := C') (norm_nonneg _) fun t hT ht => ?_
  choose u' hu' b hb hdecomp hchi hshort using fun τ => hCA τ t ht
  have ht1 : 0 < 1 + t := by linarith
  have hone : ∀ _ : ι, UpT (1 : Mt n) := fun _ => ⟨by simp, fun a c hc => Matrix.one_apply_ne hc.ne'⟩
  have hmem : (fun τ => (u' τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
    have := hst u' hu' (fun _ => 1) hone _ hbase
    simp only [Matrix.mul_one] at this
    exact this
  have h1 : f u = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u' := by
    rw [hfP u hu, ← hflow t ht, hfP u' hu', ← hP.2 _ hmem b hb]
    congr 1
    funext τ
    exact hdecomp τ
  have hq : 0 < C' / (1 + t) := div_pos hC'pos ht1
  have h2 := hK u' hu' (Real.sqrt (C' / (1 + t))) (Real.sqrt_pos.2 hq)
    (Real.sqrt_le_one.2 ((div_le_one ht1).2 (by linarith))) fun τ i =>
      Real.le_sqrt_of_sq_le ((le_div_iff₀ ht1).2 ((hshort τ i).trans (hCle τ)))
  rw [pow_mul, Real.sq_sqrt hq.le] at h2
  have h3 : ‖∏ τ, ∏ a, b τ a a ^ w τ a‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => hchi τ
  have h4 : ‖f u‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) * (K * (C' / (1 + t)) ^ (∑ τ, A τ + 1)) := by
    rw [h1, norm_mul]
    exact mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  refine (mul_le_mul_of_nonneg_right h4 ht1.le).trans_eq ?_
  rw [div_pow, pow_succ (1 + t)]
  field_simp

theorem setIntegral_translate {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (hc : ∀ a b : G, a * b = b * a) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ z, F (γ * z) = F z) (z₀ : G) :
    ∫ z in 𝓕, F (z₀ * z) ∂μ = ∫ z in 𝓕, F z ∂μ := by
  have : SMulCommClass G Γ G := ⟨fun a γ z => by
    change a * ((γ : G) * z) = γ * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  have h2 := h𝓕.smul_of_comm z₀
  rw [h𝓕.setIntegral_eq h2 fun γ z => hF γ γ.2 z]
  exact ((measurePreserving_mul_left μ z₀).setIntegral_image_emb (measurableEmbedding_mulLeft z₀) F 𝓕).symm

theorem iso_tau {D : D7} {V : HSp D} {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (ξ i)) ⬝ᵥ (gramAt D V τ).mulVec (fun i => tauE D τ (ξ i)) = 0 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h := congrArg (tauE D τ) hξ.2
  rw [map_zero] at h
  rw [← h]

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, gramAt, Matrix.map_apply, Pi.star_apply]

theorem zCusp_of_rapidDecay : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  intro D θ V S M w hθ hM φ haut hhol hdec ξ hξ μ 𝓕 hμ h𝓕 g
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace (fun x => x ∈ (ZI V ξ : Set (GA D V)))
  have : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ V).subgroupOf (ZI V ξ) => (⟨γ.1.1, γ.2⟩ : GQ V))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  obtain ⟨L, hL, hLmul, -, hUG, hLa, -, hsplit, hcomm, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨⟨ε, -⟩, -, -, hlift, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have hfin := ((GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).2.1 μ 𝓕 hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have hc : ∀ a b : ZI V ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨a, ha, u, hu, rfl⟩ := hsplit g
  have hx : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  obtain ⟨B, hB⟩ := hdec.bounded
  have hf : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w
      fun v => ∫ z in 𝓕, φ ((z : GA D V) * a * L v) ∂μ := by
    refine GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType _ _ _ _ _ w hx (ZI V ξ) (μ.restrict 𝓕) (fun z v => φ ((z : GA D V) * a * L v)) B
      (fun z => ?_) (fun z v _ => hB _) fun v _ => ?_
    · obtain ⟨f, ⟨P, hP, hfP⟩, hφf⟩ := hhol ((z : GA D V) * a)
      refine ⟨P, hP, fun v hv => ?_⟩
      beta_reduce
      rw [hφf _ (hL v hv).1, ← hfP v hv]
      congr 1
      funext τ
      exact (hL v hv).2 τ
    · exact (haut.cont.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)).measurable.aestronglyMeasurable
  have key := holFn_eq_zero hx (iso_tau hξ) hf (fun m hm v hv => ?_) (fun k => ?_) _ (hUG u)
  · simp only [hLa u hu, mul_assoc] at key
    exact key
  · obtain ⟨z₀, hz₀, hz₁, hz₂⟩ := hlift m hm
    have hm' : m = fun τ => archM V (θ τ) z₀ := funext fun τ => (hz₂ τ).symm
    have hmU : m ∈ UG (gramAt D V) := hm' ▸ hUG z₀
    have hLm : L m = z₀ := by rw [hm']; exact hLa z₀ hz₁
    refine ⟨fun τ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hmU τ) (hv τ), ?_⟩
    rw [← setIntegral_translate hc _ μ h𝓕 (fun z => φ ((z : GA D V) * a * L v)) (fun γ hγ z => ?_) ⟨z₀, hz₀⟩]
    · refine integral_congr_ae (.of_forall fun z => ?_)
      have h1 := congrArg Subtype.val (hc ⟨z₀, hz₀⟩ z)
      simp only [Subgroup.coe_mul] at h1 ⊢
      rw [hLmul m hmU v hv, hLm, h1, mul_assoc (z : GA D V) z₀, ← hcomm a ha z₀ hz₁]
      simp only [mul_assoc]
    · simp only [Subgroup.coe_mul, mul_assoc]
      exact haut.left _ hγ _
  · obtain ⟨c, N, hc0, hh⟩ := GlobalTheory.T.quotientHeight_lower_bound_short_isotropic_vector D θ V hθ ξ hξ a ha
    obtain ⟨C, hC⟩ := hdec (N * k)
    refine ⟨C / c ^ k * (μ.restrict 𝓕).real Set.univ, fun v hv δ h0 h1 hs => ?_⟩
    rw [mul_right_comm]
    refine norm_integral_le_of_norm_le_const (.of_forall fun z => ?_)
    have h2 := hh z z.2 (L v) (hL v hv).1 δ h0 h1 fun τ i => by rw [(hL v hv).2 τ]; exact hs τ i
    have h3 := pow_le_pow_left₀ hc0.le h2 k
    rw [mul_pow, ← pow_mul] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 k)]
    calc _ ≤ ‖φ ((z : GA D V) * a * L v)‖ * (δ ^ k * _) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (‖φ ((z : GA D V) * a * L v)‖ * _) * δ ^ k := by rw [mul_comm (δ ^ k), ← mul_assoc]
      _ ≤ C * δ ^ k := mul_le_mul_of_nonneg_right (hC _) (pow_nonneg h0.le _)

end GlobalTheory.HolDict.ZDecay

end
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU

section Dbl

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ κ' : Type} [Fintype κ] [Fintype κ']

end Dbl

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adm_of_eqOn_schA {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ φ ∈ schA F κ, l φ = l' φ) (hl : l ∈ (adeleClass F).adm κ) : l' ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩

variable {ψ : AddChar (AF F) ℂ} {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ κ' : Type} [Fintype κ] [Fintype κ'] {d : Darboux B κ} {d' : Darboux B κ'}
  {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
  {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem IsOp.rho_eq (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S') (w : W) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : S (d.rho ψ w φ) = d'.rho ψ w (S φ) := by
  simp only [Darboux.rho]
  rw [hS.Heisenberg₂ _ _ hφ, hs]

theorem isUSplitting_of_isOp (hψ : IsStd ψ) (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S')
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : G →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : IsUSplitting (adeleClass F) ψ d act om) : IsUSplitting (adeleClass F) ψ d' act om' := by
  have hmem : ∀ (κ₀ : Type) [Fintype κ₀] (p : (κ₀ → AF F) × (κ₀ → AF F)) (φ : (κ₀ → AF F) → ℂ),
      φ ∈ schA F κ₀ → schr ψ p φ ∈ schA F κ₀ := fun κ₀ _ p φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ₀ p φ hφ
  have hrho' : ∀ w, ∀ φ ∈ schA F κ', S' (d'.rho ψ w φ) = d.rho ψ w (S' φ) := fun w φ hφ => by
    have h1 := IsOp.rho_eq hs hS w (hS.pres' φ hφ)
    rw [hS.right φ hφ] at h1
    have hm : d.rho ψ w (S' φ) ∈ schA F κ := hmem _ _ _ (hS.pres' φ hφ)
    rw [← h1, hS.left _ hm]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ' hμ' g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [hom g φ hφ]
    exact hS.pres _ (h.pres g _ (hS.pres' φ hφ))
  · have hw : d'.rho ψ w φ ∈ schA F κ' := hmem _ _ _ hφ
    rw [hom g _ hw, hrho' w φ hφ, h.impl g w _ (hS.pres' φ hφ),
      IsOp.rho_eq hs hS _ (h.pres g _ (hS.pres' φ hφ)), hom g φ hφ]
  · have h2 := hS.adm' _ (h.adm g _ (hS.adm l hl))
    refine adm_of_eqOn_schA (fun φ hφ => ?_) h2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]
  · letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    obtain ⟨c, -, -, hc⟩ := hS.norm Measure.addHaar μ' inferInstance hμ'
    rw [hom g φ hφ, hc _ (h.pres g _ (hS.pres' φ hφ)), h.unit Measure.addHaar inferInstance g _ (hS.pres' φ hφ),
      ← hc _ (hS.pres' φ hφ), hS.right φ hφ]
  · refine (h.cont (l ∘ₗ S) (hS.adm l hl) (S' φ) (hS.pres' φ hφ)).congr fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]

theorem siegelRule_of_isOp {E' : Type} [CommRing E'] [Algebra (AF F) E'] {c : E' →ₐ[AF F] E'} {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E'} {JA : Matrix α α E'} {JB : Matrix β β E'}
    {d : Darboux (symp c ξ JA JB) κ} {d' : Darboux (symp c ξ JA JB) κ'} (hs : ∀ w, s (d.e w) = d'.e w)
    (hS : IsOp ψ s S S') {χ : E'ˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E'}
    {om : UG c JB →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : UG c JB →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : SiegelRule c (adeleClass F) ψ ξ JA JB d χ Cy om) : SiegelRule c (adeleClass F) ψ ξ JA JB d' χ Cy om' := by
  intro l hl hinv p t hpt φ hφ
  have key := h (l ∘ₗ S) (hS.adm l hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [IsOp.rho_eq hs hS _ hφ']
    exact hinv z _ (hS.pres _ hφ')) p t hpt (S' φ) (hS.pres' φ hφ)
  simp only [LinearMap.coe_comp, Function.comp_apply, hS.right φ hφ] at key
  rw [hom p φ hφ]
  exact key

end Adelic

end GlobalTheory.TowU

end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.NoethGens

theorem exists_cover (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) (d : ℕ) :
    ∀ Z : Set X, IsClosed Z → (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) < d) →
      ∃ (e : ℕ) (x : Fin d → X.functionField), 0 < e ∧ (∀ l, x l ∈ P.H e 0) ∧ ∀ z ∈ Z, ∃ l, z ∈ NV P e 0 (x l) := by
  induction d with
  | zero =>
    intro Z _ h
    refine ⟨1, Fin.elim0, one_pos, fun l => l.elim0, fun z hz => ?_⟩
    exfalso
    have h₁ := h (ringChar (X.residueField z))
    have hne : Nonempty ↥(Z ∩ fib X (ringChar (X.residueField z))) := ⟨⟨z, hz, rfl⟩⟩
    obtain ⟨w⟩ := hne
    have hne' : Nonempty (IrreducibleCloseds ↥(Z ∩ fib X (ringChar (X.residueField z)))) :=
      ⟨⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Z ∩ fib X (ringChar (X.residueField z))) :=
      Order.krullDim_nonneg
    exact absurd h₁ (not_lt.2 (by simpa using h₂))
  | succ d ih =>
    intro Z hZ h
    obtain ⟨e, he, f, hf, hlt⟩ := GlobalTheory.T.exists_section_lowering_fibre_dimension k X p D hX P hP d Z hZ fun ℓ =>
      ENat.WithBot.lt_add_one_iff.1 (by simpa using h ℓ)
    have hnf := GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 f hf
    obtain ⟨e', x, he', hx, hc⟩ := ih (Z \ NV P e 0 f) (hZ.sdiff hnf.1) hlt
    have c₁ : ((e' * e : ℕ) : ℤ) = (e' : ℤ) * (e : ℤ) := Nat.cast_mul _ _
    have c₂ : ((e' * e : ℕ) : ℤ) = (e : ℤ) * (e' : ℤ) := by rw [c₁, mul_comm]
    refine ⟨e' * e, Fin.cons (f ^ e') fun l => x l ^ e, Nat.mul_pos he' he, fun l => ?_, fun z hz => ?_⟩
    · refine Fin.cases ?_ (fun l => ?_) l
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e 0 f hf e').1
        rw [mul_zero, ← c₁] at this
        simpa only [Fin.cons_zero] using this
      · have := (GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P e' 0 (x l) (hx l) e).1
        rw [mul_zero, ← c₂] at this
        simpa only [Fin.cons_succ] using this
    · by_cases hzf : z ∈ NV P e 0 f
      · refine ⟨0, ?_⟩
        have := hnf.2.2.1 e' he'
        rw [mul_zero, ← c₁] at this
        rw [Fin.cons_zero, this]
        exact hzf
      · obtain ⟨l, hl⟩ := hc z ⟨hz, hzf⟩
        refine ⟨l.succ, ?_⟩
        have := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e' 0 (x l) (hx l)).2.2.1 e he
        rw [mul_zero, ← c₂] at this
        rw [Fin.cons_succ, this]
        exact hl

theorem exists_gens (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hP : IsAmpleLB P.L.B) :
    ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  obtain ⟨e, x, he, hx, hc⟩ := exists_cover k X p D hX P hP (D + 1) Set.univ isClosed_univ fun ℓ => by
    rw [Set.univ_inter, Nat.cast_add_one]
    exact ENat.WithBot.lt_add_one_iff.2 ((GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX).2.2.2.1 ℓ)
  exact ⟨e, x, he, hx, fun z => hc z trivial⟩

end GlobalTheory.HSAmp.NoethGens
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.polynomialFockSpace_eq_range_fockMap_variable_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (P Q R S : InfinitePlace F → ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm (P w) (Q w)) →
    (∀ w, W.θ w * C w = C w * Jm (R w) (S w)) → IsFockMapD ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ := by
  first | exact @GlobalTheory.HoweD.PolRangeD.polRangeD | exact GlobalTheory.HoweD.PolRangeD.polRangeD | (intros; apply GlobalTheory.HoweD.PolRangeD.polRangeD <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel : Quoted → RankLow := by
  first | exact @GlobalTheory.HSCore.RankBound.rankLow | exact GlobalTheory.HSCore.RankBound.rankLow | (intros; apply GlobalTheory.HSCore.RankBound.rankLow <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (P0 : Polynomial G.F) (μ : ℂ) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → Irreducible P0 → P0.eval₂ v.embedding μ = 0 → ∃ A : Polynomial G.F, (∀ Q : DPair G, Q.pol = P0 → ∃ P : Pair G, P.γ = Q.γ ∧ P.c = Q.c ∧ (P.β : G.C) = Polynomial.aeval (Q.γ : G.C) A * Q.β ∧ P.Mark μ ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) ∧ (∀ P : Pair G, P.pol = P0 → P.Mark μ → ∃ Q : DPair G, Q.γ = P.γ ∧ Q.c = P.c ∧ (P.β : G.C) = Polynomial.aeval (P.γ : G.C) A * Q.β ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) := by
  first | (exact @GlobalTheory.LKDef.move_definite) | (exact GlobalTheory.LKDef.move_definite) | (intros; apply GlobalTheory.LKDef.move_definite  <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.centraliser_compactPart_le_integral_almostAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  first | exact @GlobalTheory.BCT.GoodCpt.main | exact GlobalTheory.BCT.GoodCpt.main | (intros; apply GlobalTheory.BCT.GoodCpt.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inf_fixedVectors_adelicLevel_ne_bot_of_localLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  first | exact @GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | exact GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | (intros; apply GlobalTheory.FixLev.inf_fixed_globLev_ne_bot <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem reads_linear_injective_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx f f' φ φ' hf hf'
  obtain ⟨-, -, hlin⟩ := thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hS hev x hx φ hf.1
  obtain ⟨hl, hinj⟩ := hlin φ' hf'.1
  obtain ⟨-, -, -, -, hp⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x
  obtain ⟨p, -, hp, -⟩ := hp hx
  refine ⟨fun a b => ⟨(hl a b).1, fun w hw => ?_⟩, fun h => hinj ?_, fun h h' e => ?_⟩
  · rw [(hl a b).2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.2 w hw, hf'.2 w hw]
    ring
  · funext z
    have h1 := hf.2 (p z) (hp z).1
    have h2 := hf'.2 (p z) (hp z).1
    rw [h, h2, (hp z).2] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm
  · refine theta_eq_of_real D ψ V W hψ f f' h h' fun w hw => ?_
    rw [hf.2 w hw, hf'.2 w hw, e]

theorem IsONFr.mem_dom {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}
    (hx : IsONFr X x) : x ∈ X.dom :=
  PIW.FdPA.orthonormal_domain r X x hx

theorem reads_linear_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx
  exact reads_linear_injective_dom D ψ θ V W r g hr X bas idx hψ hθ hV hev hM hS x hx.mem_dom

end GlobalTheory.AdTh
end
