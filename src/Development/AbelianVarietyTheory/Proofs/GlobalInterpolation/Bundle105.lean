module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle072
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle088
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle098
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle099
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle100
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ}

namespace PtModel

variable (M : PtModel X i)

theorem inc_eq_image (v : X.A.vT) (p : M.Pt) :
    {p₁ | M.Inc v p p₁} =
      (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) '' {q | (p.2 v).Inc q} := by
  ext p₁
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p₁.2 v, h3, ?_⟩
    refine Prod.ext h1.symm ?_
    funext v'
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Function.update_of_ne hv, h2 v' hv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩
    simpa using hq

theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

theorem finsum_inc_comm (v v' : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v' p₁ p₂}, F p₂) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v' p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v p₁ p₂}, F p₂ := by
  by_cases hv : v = v'
  · subst hv; rfl
  have hv' : v' ≠ v := fun h => hv h.symm
  rw [finsum_inc_eq, finsum_inc_eq]
  simp only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']
  rw [finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]
  simp only [Function.update_comm hv]

end PtModel

theorem formsStable_of_tgtEq : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → FormsStable X := by
  intro D u X Lv Kt hK
  refine ⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) _).2 ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' φ Φ hΦ)
    have h2 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ)
    funext c
    rw [h1.1 c, h2.1 c]
    simp only []
    rw [(Lv i hi).finsum_inc_comm v v']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi.le) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X (i + 1) (Lv (i + 1) hi) _).2
      ⟨_, GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩

end GlobalTheory.LvT
end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT

theorem count_incidence {G P C V : Type} [Group G] [MulAction G P] [Fintype C] [AddCommGroup V] [Module ℂ V]
    (rep : C → P) (hsurj : ∀ p, ∃ (c : C) (g : G), g • rep c = p)
    (hinj : ∀ (c c' : C) (g : G), g • rep c = rep c' → c = c')
    (hfin : ∀ c, Finite (MulAction.stabilizer G (rep c)))
    (I : P → P → Prop) (hup : ∀ p, {q | I p q}.Finite) (hdn : ∀ p, {q | I q p}.Finite)
    (hI : ∀ (g : G) p q, I p q → I (g • p) (g • q))
    (F : P → P → V) (hF : ∀ (g : G) p q, F (g • p) (g • q) = F p q) :
    ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ q ∈ {q | I (rep c) q}, F (rep c) q =
      ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ p ∈ {p | I p (rep c)}, F p (rep c) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  have hfin' : ∀ p : P, Finite (MulAction.stabilizer G p) := by
    intro p
    obtain ⟨c, g, rfl⟩ := hsurj p
    haveI := hfin c
    exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv
  have hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a := by
    intro a
    obtain ⟨c, g, rfl⟩ := hsurj a
    refine ⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩
    rintro r ⟨hr, γ, hγ⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c = c' := hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)
    rw [this]
  have hrinj : Function.Injective rep := fun c c' h => hinj c c' 1 (by rw [one_smul, h])
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F
    (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp)
    (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢; exact hI γ a b h)
    (fun γ a b _ => hF γ a b) hfin' hfin' hR hR
  rw [Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)] at key
  have hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x := by
    intro n x
    change (algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _
    simp
  simp only [hq] at key
  simp only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]
  exact key

theorem levelChainUOperatorCommutation_of_pointPairLaw : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → (∀ i h, (Kt i h).UKLaw) → LevelChainUOperatorCommutation X := by
  intro D u X Lv Kt htgt huk i hi v φ hφ
  set M := Lv i hi.le with hM
  set M' := Lv (i + 1) hi with hM'
  let K : KerPt M M' := Kt i hi
  have hT : K.TgtEq := htgt i hi
  have hU : K.UKLaw := huk i hi
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  obtain ⟨hfinI, hstab, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  obtain ⟨hfinI', -, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X (i + 1) M' v
  have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X (i + 1) M' v _ _ (GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K φ Φ hT hΦ)
  have h2 := GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K _ _ hT (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ)
  have hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2) := by
    obtain ⟨k, hk⟩ := D.R.t_odd
    have e1 : (D.R.t + 1) / 2 = k + 1 := by omega
    have e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [e1, e2, Real.rpow_natCast]
    push_cast; rfl
  have hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹ := by
    intro c
    rw [← M.card_stab]; rfl
  have hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c)) := by
    intro c
    apply Nat.finite_of_card_ne_zero
    rw [← M.card_stab]
    haveI := X.C.stabFin i c
    letI := X.C.stabGrp i c
    exact Nat.card_pos.ne'
  funext c'
  rw [hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]
  congr 1
  have key := count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2)
    (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q))
    (fun g p q => by rw [hΦ.2, K.src])
  have hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁) := by
    intro c

    rw [finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]
  simp only [hL, hwt]
  rw [key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]

end GlobalTheory.LvT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.heisenbergCocycleForm_integral_selfDual : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.CocInt.cocycle_integral | exact GlobalTheory.MomT.CocInt.cocycle_integral | (intros; apply GlobalTheory.MomT.CocInt.cocycle_integral <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.LiftTranslate

theorem signed_eq {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) (hα : ∀ x, α (-x) = α x)
    {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α B)
    {s u : V} (h1 : s ∈ A) (h2 : u ∈ A) (h3 : u - s ∈ B) (z : V) :
    α s * opU H (-s) θ z = α u * opU H (-u) θ z := by
  have h := GlobalTheory.ThetaInter.alpha_opU_add hH hd hs (A.neg_mem h2) (A.sub_mem h2 h1) θ z
  rw [show -u + (u - s) = -s by abel, hα, hα, ← GlobalTheory.ThetaInter.opU_mul (-u) (α (u - s)),
    show (fun w => α (u - s) * opU H (u - s) θ w) = θ from funext (hθ _ h3)] at h
  exact h

theorem alV_neg {ι : Type} [Fintype ι] {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV ι a b) : alV d sc (-x) = alV d sc x := by
  simp [alV, alphaQ, Formalism.L2.Th1.H.qOf]

private theorem sdLat_span_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) :
    Submodule.span E (L : Set (Sp E n)) = ⊤ := by
  let W := Submodule.span E (L : Set (Sp E n))
  change W = ⊤
  by_contra h
  let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
  let g : Sp E n →ₗ[E] Module.Dual E W :=
    (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
  have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  have hsmul (a : E) : a • e x ∈ L := by
    rw [← hL.2, dualBasic_mem_dual]
    intro y hy
    apply hStd_mem_one_symm
    have hxy : hStd E n (e x) y = 0 :=
      congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [StarRing E] in
theorem nat_smul_mem {M : Submodule (𝓞 E) (HomE E a b)} (c : ℕ) {y : HomE E a b} (hy : y ∈ M) : (c : E) • y ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]
  exact M.toAddSubgroup.nsmul_mem hy c

theorem off_le (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) {c c' : ℕ} (hc : 0 < c) (hc' : 0 < c')
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ∉ S) {y : HomE E a b} (hy : y ∈ localization₂ Q.asIdeal (halfAO S M c')) :
    y ∈ localization₂ Q.asIdeal (twist₂ M c (expS S)) := by
  have hcE : (c' : E) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [halfAO, mem_localization_twist M hc' (fun Q => by have := expS_bound S Q; omega)] at hy
  rw [mem_localization_twist M hc (expS_bound S)]
  unfold expS at hy ⊢
  rw [if_neg hQ] at hy ⊢
  split_ifs at hy ⊢
  · have h1 := nat_smul_mem c' hy
    rw [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h1
    rw [zpow_neg, inv_inv, zpow_one]
    exact nat_smul_mem c h1
  · simpa using hy

theorem mem_mulLat_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hAA : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {c : ℕ} (hc : 0 < c) (y : HomE E a b) :
    y ∈ mulLat c (homAt S N N') ↔ ∀ P ∈ S, y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ∀ P ∈ S, (y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) ↔ (c : E)⁻¹ • y ∈ homAt {P} N N') := by
    intro P hP
    rw [mem_localization_twist _ hc (expS_bound S), (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P N N' hN (hAA P hP), expS,
      if_pos hP, zpow_one]
  have hsm : ∀ w : HomE E a b, (c : 𝓞 E) • w = (c : E) • w := fun w => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · rintro ⟨w, hw, rfl⟩ P hP
    rw [key P hP, LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, inv_mul_cancel₀ hcE, one_smul]
    intro P' hP'
    rw [Finset.mem_singleton.1 hP']
    exact hw P hP
  · intro h
    refine ⟨(c : E)⁻¹ • y, fun P hP => (key P hP).1 (h P hP) P (Finset.mem_singleton_self P), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, mul_inv_cancel₀ hcE, one_smul]

end Loc

theorem signed_liftW_eq : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N G : Submodule (𝓞 X.E) (Sp X.E a)) (N' G' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x t : HomE X.E a b) (θ : VCx X.Tau a b → ℂ), Moves A a b → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → IsSdLat G → IsSdLat G' → 0 < c → Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S))) → t ∈ perO A.AA G G' → t - x ∈ mulLat c (homAt S N N') → θ ∈ fixedBy (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N (twist₂ N' c (expS S))) → ∀ z, (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x)) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x))) θ z = (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) t) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) t)) θ z := by
  intro X A a b S N G N' G' c x t θ hM hS hAA hN hN' hG hG' hc hD ht htx hθ z
  obtain ⟨hδ, -, -, hA0, hLa, -⟩ := hM
  have hfg : N.FG := hN.1.fg
  have per := GlobalTheory.ThetaMove.PeriodComp.perO_components X.E a b A.AA
  have eB : twist₂ (perO A.AA N N') c (expS S) = perO A.AA N (twist₂ N' c (expS S)) :=
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ hfg hc (expS_bound S)
  have eA : ∀ c' : ℕ, 0 < c' → halfAO S (perO A.AA N N') c' = perO A.AA N (twist₂ N' c' fun Q => -expS S Q) := fun c' hc' =>
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c' _ hfg hc' (fun Q => by have := expS_bound S Q; omega)
  have sdB := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS hN' hc).1
  have sdA := fun c' (hc' : 0 < c') => (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c' S hS hN' hc').2
  have fullSd {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) (hL : IsSdLat L) :
      Submodule.IsFullLattice X.E L := by
    letI : Submodule.IsLattice X.E L := hL.1
    exact ⟨sdLat_span_local L hL⟩
  have fB : Full (twist₂ (perO A.AA N N') c (expS S)) := eB ▸ per.2.2 N _ hfg (fullSd _ sdB) hA0
  have fA : ∀ c' : ℕ, 0 < c' → Full (halfAO S (perO A.AA N N') c') := fun c' hc' => by
    rw [eA c' hc']; exact per.2.2 N _ hfg (fullSd _ (sdA c' hc')) hA0
  have fG : Full (perO A.AA G G') := per.2.2 G G' hG.1.fg (fullSd _ hG') hA0
  have hmul := mem_mulLat_iff S A.AA N N' hfg hAA hc
  have hex : ∃ s, A.IsLift S N N' c x s := by
    obtain ⟨c', hc', hx⟩ := per.2.2 N N' hfg (fullSd _ hN') hA0 x
    obtain ⟨s, h1, h2⟩ := ((fA c' hc').inf fB).approx S x
    simp only [localization_inf, Submodule.mem_inf] at h1 h2
    refine ⟨s, ⟨c', hc', mem_of_locP fun Q => ?_⟩, (hmul _).2 fun P hP => (h1 P hP).2⟩
    by_cases hQ : Q ∈ S
    · have h3 : x ∈ localization₂ Q.asIdeal (halfAO S (perO A.AA N N') c') := by
        rw [halfAO, mem_localization_twist _ hc' (fun Q => by have := expS_bound S Q; omega), expS, if_pos hQ, zpow_neg, inv_inv, zpow_one,
          Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
        exact mem_localization_of_mem Q hx
      simpa using add_mem (h1 Q hQ).1 h3
    · exact (h2 Q hQ).1
  obtain ⟨⟨c₁, hc₁, hs⟩, hsx⟩ : A.IsLift S N N' c x (A.liftW S N N' c x) := Classical.epsilon_spec hex
  generalize A.liftW S N N' c x = s at hs hsx ⊢
  rw [hmul] at hsx htx
  rw [← eB] at hD
  obtain ⟨u, h1, h2⟩ := (((fA c₁ hc₁).inf fG).inf fB).approx S s
  simp only [localization_inf, Submodule.mem_inf] at h1 h2
  have huA : u ∈ halfAO S (perO A.AA N N') c₁ := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (h1 Q hQ).1.1 (mem_localization_of_mem Q hs)
    · exact (h2 Q hQ).1.1
  have hus : u - s ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact (h1 Q hQ).2
    · exact sub_mem (h2 Q hQ).2 (off_le S _ hc hc₁ hQ (mem_localization_of_mem Q hs))
  have hut : u - t ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · rw [show u - t = (u - s) + (s - x) - (t - x) by abel]
      exact sub_mem (add_mem (h1 Q hQ).2 (hsx Q hQ)) (htx Q hQ)
    · exact sub_mem (h2 Q hQ).2 (hD.2 Q hQ (mem_localization_of_mem Q ht))
  have huG : u ∈ perO A.AA G G' := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (hD.1 Q hQ (mem_localization_of_mem Q hut)) (mem_localization_of_mem Q ht)
    · exact (h2 Q hQ).1.2
  rw [eB] at hus hut
  rw [eA c₁ hc₁] at hs huA
  have L1 := (hLa N _ hN (sdA c₁ hc₁)).2.2
  have L2 := (hLa G G' hG hG').2.2
  have im : ∀ {M : Submodule (𝓞 X.E) (HomE X.E a b)} {y}, y ∈ M → embH (X.embC A.σ₀) A.δ y ∈ laV (X.embC A.σ₀) A.δ M :=
    fun hy => ⟨_, hy, rfl⟩
  rw [signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L1.1 L1.2 hθ (im hs) (im huA) (by rw [← map_sub]; exact im hus),
    signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L2.1 L2.2 hθ (im ht) (im huG) (by rw [← map_sub]; exact im hut)]

end GlobalTheory.ThetaMove.LiftTranslate
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.conjugate_embeddings_induce_different_primes_split : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧ 1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  first | exact @GlobalTheory.ConjPlace.conj_place_ne | exact GlobalTheory.ConjPlace.conj_place_ne | (intros; apply GlobalTheory.ConjPlace.conj_place_ne <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.complexPadic_norm_kappa_splitPrime : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  first | exact @GlobalTheory.KapSplitNorm.norm_kappa_split | exact GlobalTheory.KapSplitNorm.norm_kappa_split | (intros; apply GlobalTheory.KapSplitNorm.norm_kappa_split <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.exists_realAdelicHermitian_signature_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  first | exact @GlobalTheory.RealSpaceCoord.exists_coord | exact GlobalTheory.RealSpaceCoord.exists_coord | (intros; apply GlobalTheory.RealSpaceCoord.exists_coord <;> assumption)
end
